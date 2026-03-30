mod consistency;
mod transcript;
mod public_secret_inner_product;
// use bulletproofs::{BulletproofGens, PedersenGens, RangeProof};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use sunscreen_bulletproofs::{BulletproofGens, GeneratorsChain, PedersenGens};
use curve25519_dalek::scalar::Scalar;
use merlin::Transcript;
use rand::thread_rng;
use std::{collections::HashMap, result};
// from logproof
use seal_fhe::{
    BFVScalarEncoder, BfvEncryptionParametersBuilder, Ciphertext, CoefficientModulus, Context, Decryptor, EncryptionParameters, Encryptor, KeyGenerator, PlainModulus, PublicKey, SecretKey, SecurityLevel,ToBytes
};
use std::borrow::Cow;
use sunscreen_math::{
    poly::Polynomial,
    ring::{BarrettBackend, BarrettConfig, Ring, Zq},
};
use logproof::{
    bfv_statement::{generate_prover_knowledge, BfvMessage, BfvProofStatement, BfvWitness},
    linear_algebra::Matrix,
    Bounds, 
    LogProofProverKnowledge,
    LogProofGenerators,
    math::rand256,
};
// change the rings parameters d=1024, d=2048, d=4096
use logproof::rings::SealQ128_1024;
// use logproof::rings::SealQ128_2048;
// use logproof::rings::SealQ128_4096;
use std::time::Instant;
use crate::consistency::{ConsProof, ConsProverKnowledge, ConsVerifierKnowledge};
const TRANSCRIPT_LABEL: &'static [u8] = b"bfv-and-commitment";



#[derive(Clone, Debug)]


/// new transaction type
pub struct ConversionTx {
    pub user: String,
    pub pc_commitments: Vec<CompressedRistretto>,
    pub fhe_ciphertexts: Vec<Ciphertext>,
}

// ---(Pedersen Ledger) ---
pub struct ConfidentialChain {
    pub ctx: ConversionTx,
}


// --- client (Account) ---
pub struct Account {
    pub name: String,
    pub value: u64,
    pub blinding: Scalar,
    pub pk: PublicKey,
    sk: SecretKey,
    pub ctx_bfv: Context,
    pub params: EncryptionParameters,
    pub f: RistrettoPoint,
    pub u: RistrettoPoint,
}

impl Account {
    pub fn new(name: &str, initial_value: u64) -> (Self, CompressedRistretto) {
        let u = PedersenGens::default().B_blinding;
        let f = PedersenGens::default().B;
        let blinding = Scalar::random(&mut thread_rng());
        let initial_value_scalar = Scalar::from(initial_value);
        let commitment = Self::compute_ctx_gens_commitment(&f, &u, &initial_value_scalar, &blinding);
        // 1. setting BFV parameters
        // the parameter 1024 can be changed to 2048, or 4096
        let plain_modulus = PlainModulus::raw(512).unwrap();
        let coeff_modulus = CoefficientModulus::bfv_default(1024, SecurityLevel::TC128).unwrap();
        let params = BfvEncryptionParametersBuilder::new()
            .set_poly_modulus_degree(1024)
            .set_coefficient_modulus(coeff_modulus)
            .set_plain_modulus(plain_modulus)
            .build()
            .unwrap();
        let ctx_bfv = Context::new(&params, false, SecurityLevel::TC128).unwrap();
        let key_gen = KeyGenerator::new(&ctx_bfv).unwrap();
        // 3. generate key pair
        let keygen_start = Instant::now();
        let pk = key_gen.create_public_key();
        let sk = key_gen.secret_key();
        println!("key generation took: {:?}", keygen_start.elapsed());
        (Self {
            name: name.to_string(),
            value: initial_value,
            blinding,
            pk,
            sk,
            ctx_bfv,
            params,
            f,
            u
        }, commitment)
    }

    

    /// core functionality: proof of equality
    pub fn create_conversion_to_fhe(
        &self,
        messages: Vec<u64>,
    ) -> Result<ConversionTx, &'static str> {
        let proof_start = Instant::now();
        
        let mut pc_commitments = Vec::new();
        let mut fhe_ciphertexts = Vec::new();
        let mut fhe_components_vec = Vec::new();
        
        let mut blindings = Vec::new();
        let encryptor = Encryptor::with_public_and_secret_key(&self.ctx_bfv, &self.pk, &self.sk).unwrap();
        let decryptor = Decryptor::new(&self.ctx_bfv, &self.sk).unwrap();
        // Generate plaintext data
        let encoder = BFVScalarEncoder::new();

        println!("[Account] starts {} messages to generate proof of equality...", messages.len());

        for &m in &messages {
            // generate Pedersen commitment
            let r = Scalar::random(&mut thread_rng());
            let m_scalar = Scalar::from(m);
            let commitment = Self::compute_ctx_gens_commitment(&self.f, &self.u, &m_scalar, &r);
            pc_commitments.push(commitment);
            blindings.push(r);

            // Generate plaintext data
            let plaintext = encoder.encode_unsigned(m).unwrap();
            let (ciphertext, components) = encryptor.encrypt_return_components(&plaintext).unwrap();
            let ciphertext_bytes = ciphertext.as_bytes().expect("fail to serialize");

            println!("--- serializing (including ZStd compression) ---");
            println!("bytes of ciphertexts after compression: {} B", ciphertext_bytes.len());
            println!("kilo bytes of ciphertexts after compression: {:.2} KB", ciphertext_bytes.len() as f64 / 1024.0);
            let decrypt_start = Instant::now();
            let decrypted = decryptor.decrypt(&ciphertext).unwrap();
            let data = encoder.decode_unsigned(&decrypted).unwrap();
            println!("retrive algorithm took: {:?}", decrypt_start.elapsed());
            assert_eq!(m, data, "decryption failed.");
            fhe_ciphertexts.push(ciphertext);
            fhe_components_vec.push(components);
        }

        // 1. prepare messages
        let mut bfv_messages = Vec::new();

        for &m in &messages {
            let plaintext = encoder.encode_unsigned(m).unwrap();
            
            bfv_messages.push(BfvMessage {
                plaintext,
                bounds: None,
            });
        }

        // 2. prepare Statement
        let mut statements = Vec::new();
        for (i, ct) in fhe_ciphertexts.iter().enumerate() {
            statements.push(BfvProofStatement::PublicKeyEncryption {
                message_id: i,
                ciphertext: ct.clone(),
                public_key: Cow::Borrowed(&self.pk),
            });
        }

        // 3. prepare Witness
        let witnesses: Vec<BfvWitness> = fhe_components_vec
            .into_iter()
            .map(|comp| BfvWitness::PublicKeyEncryption(comp))
            .collect();
        // change the rings parameters
        // for SealQ128_2048, change <_, SealQ128_1024, 1> to <_, SealQ128_2048, 1>
        // for SealQ128_4096, change <_, SealQ128_1024, 1> to <_, SealQ128_4096, 2>
        let proverknowledge = generate_prover_knowledge::<_, SealQ128_1024, 1>(
            &statements,    // &[BfvProofStatement]
            &bfv_messages,  // &[BfvMessage]
            &witnesses,     // &[BfvWitness]
            &self.params,
            &self.ctx_bfv,
        );

        let cons_verifierknowledge = ConsVerifierKnowledge {
            a: proverknowledge.vk.a,
            t: proverknowledge.vk.t,
            bounds: proverknowledge.vk.bounds,
            f: proverknowledge.vk.f,
        };

        let cons_proverknowledge  = ConsProverKnowledge {
            s: proverknowledge.s,
            vk: cons_verifierknowledge.clone(),
        };

        let gens_len = cons_verifierknowledge.l() as usize;
        let setup_start = Instant::now();
        let cons_gens = LogProofGenerators::new(gens_len);
        println!("System Setup took: {:?}", setup_start.elapsed());

        let mut transcript = Transcript::new(TRANSCRIPT_LABEL);
        
        let shared_indices = vec![(0 as usize,0 as usize)];
        let half_rho = Scalar::from_bits(rand256());
        let proof = ConsProof::create_with_shared(& mut transcript, &cons_proverknowledge, &cons_gens.g, &cons_gens.h, &self.u, &half_rho, &shared_indices, &self.f, &pc_commitments, &blindings);
        println!("requestsc took: {:?}", proof_start.elapsed());
        let verify_start = Instant::now();
        let mut verify_trans = Transcript::new(TRANSCRIPT_LABEL);
        let result = proof.verify(& mut verify_trans, &cons_verifierknowledge, &cons_gens.g, &cons_gens.h, &self.u,&self.f, &pc_commitments);
        match result {
            Ok(_) => println!("✅ check pass！"),
            Err(e) => println!("❌ check fail: {:?}", e),
        }
        println!("verify took: {:?}", verify_start.elapsed());

        Ok(ConversionTx {
            user: self.name.clone(),
            pc_commitments,
            fhe_ciphertexts,
        })
    }

    pub fn compute_ctx_gens_commitment(
        f: &RistrettoPoint,
        g: &RistrettoPoint,
        v: &Scalar,
        blinding: &Scalar,
    ) -> CompressedRistretto {
        let commit = v * f + blinding * g;
        commit.compress()
    }
}


fn main() {

    let (mut alice, alice_comm) = Account::new("Alice", 1000);
    let (mut bob, bob_comm) = Account::new("Bob", 500);

    println!(">>> Initial State: Alice=1000, Bob=500 (Encrypted on chain)");
    

    let messages = vec![42];
    
    println!("\n>>> Generating PC and BFV compatibility transaction...");

    match alice.create_conversion_to_fhe(messages.clone()) {
        Ok(tx) => {}
        Err(e) => println!("运行出错: {}", e),
    }
}
