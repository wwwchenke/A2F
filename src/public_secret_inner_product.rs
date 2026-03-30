use std::time::Instant;

use curve25519_dalek::{
    ristretto::{CompressedRistretto, RistrettoPoint},
    scalar::Scalar,
    traits::MultiscalarMul,
};
use digest::ExtendableOutput;
use digest::XofReader;
use log::trace;
use merlin::Transcript;
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use sha3::{digest::Update, Shake256};

use sunscreen_math::{RistrettoPointVec, ScalarVec};

use logproof::ProofError;
use logproof::{linear_algebra::InnerProduct, math::rand256};
use logproof::{math::parallel_multiscalar_multiplication};
use crate::{
    transcript::ConsProofTranscript,
};

#[derive(Debug, Clone)]
/**
 * Information known to both the prover and verifier.
 */
pub struct IPSPVerifierKnowledge {
    /**
     * A commitment to g^v_1 * f^x * u^rho
     */
    pub t: RistrettoPoint,

    /**
     * The public vector v_2.
     */
    pub z: Vec<Scalar>,
}

#[derive(Debug, Clone)]
/**
 * Information known only to the prover.
 */
pub struct IPSPProverKnowledge {
    /**
     * The secret vector of the inner product.
     */
    v_1: Vec<Scalar>,

    /**
     * A blinding factor;
     */
    rho: Scalar,

    /**
     * The knowledge shared between both the prover and verifier
     */
    pub vk: IPSPVerifierKnowledge,
}

impl IPSPProverKnowledge {
    /**
     * Create a new [`IPSPProverKnowledge`].
     */
    pub fn new(v_1: &[Scalar], v_2: &[Scalar], rho: &Scalar, t: &RistrettoPoint) -> Self {
        assert_eq!(v_1.len(), v_2.len());
        assert!(!v_1.is_empty());

        let vk = IPSPVerifierKnowledge { t: t.to_owned(), z: v_2.to_vec() };

        Self {
            v_1: v_1.to_owned(),
            rho: *rho,
            vk,
        }
    }

    /**
     * A handy function to generate a commitment to v_1 and v_2.
     * This is the `t` input to the verifier's knowledge.
     */
    pub fn make_commitment(
        v_1: &[Scalar],
        vec_z: &[Scalar],
        rho: &Scalar,
        f: &RistrettoPoint,
        h: &[RistrettoPoint],
        u: &RistrettoPoint,
    ) -> RistrettoPoint {
        // compute res = h_0^v_1_0 + ... + h_n^v_1_n + f^<v_1,vec_z> + u^rho
    // 1. check the length
        assert_eq!(v_1.len(), h.len(), "v_1 and h must have the same length");
        assert_eq!(v_1.len(), vec_z.len(), "v_1 and vec_z must have the same length");

        // 2. compute inner product <v_1, vec_z>
        // ip = sum(v_1_i * vec_z_i)
        let ip: Scalar = v_1.iter()
            .zip(vec_z.iter())
            .map(|(a, b)| a * b)
            .sum();

        // 3. use MultiscalarMul
        let scalars = v_1.iter()
            .chain(std::iter::once(&ip))
            .chain(std::iter::once(rho));
            
        let points = h.iter()
            .chain(std::iter::once(f))
            .chain(std::iter::once(u));

        RistrettoPoint::multiscalar_mul(scalars, points)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
/**
 * A zero-knowledge proof that the provers knows vectors `v_1` and `x`, apublic vector v_2(vec_z)
 * whose inner product is `x`. `x` is public
 *
 * # Remarks
 * Unlike the original Bulletproofs inner product proof,
 * this version is modified to be zero-knowledge. This allows for simpler
 * range proofs.
 */
pub struct IPSPInnerProductProof {
    /// commit poly t(x): t_1
    pub t_1: Vec<CompressedRistretto>,
    /// commit poly t(x): t_minus1
    pub t_minus1: Vec<CompressedRistretto>,
    /// inner product result w
    pub w: CompressedRistretto,
    /// response value e_1
    pub e_1: Scalar,
    /// response value e_2
    pub e_2: Scalar,
}

impl IPSPInnerProductProof {
    /**
     * Create an inner product proof that `dot(pk.v_1, vk.v_2) == pk.x`. That
     * is, prove you know 2 secret `v_1` and `x` and a public vector 'v_2' whose inner product
     * is public `x`.
     *
     * # Remarks
     * `g`, `h` are slices of generators whose length must equal `pk.v_1.len()`.
     * `u` is a generator used in the commitment's blinding term.
     *
     * The vanilla algorithm requires v_2.len() be a power of 2, but this
     * implementation allows any non-zero length vectors. In such cases,
     * this method will effectively pad v_1 and v_2 with zeros to the next power
     * of two. This does not change the inner product.
     *
     * # Panics
     * If any of `g.len() != h.len() != pk.v_1.len() != pk.v_2.len()`.
     */
    
    pub fn create(
        transcript: &mut Transcript,
        pk: &IPSPProverKnowledge,
        gens_f: &RistrettoPoint,
        h: &[RistrettoPoint],
        u: &RistrettoPoint,
    ) -> Self {
        let mut pk = pk.clone();
        assert_eq!(pk.v_1.len(), pk.vk.z.len());
        assert_eq!(h.len(), pk.v_1.len());

        let len = h.len().next_power_of_two();
        let old_len = h.len();

        // Extend v_1, v_2, g, h to be a power of 2. Append zeros to v*
        // and any point to g, h.
        let h = [h, &vec![RistrettoPoint::default(); len - old_len]].concat();
        pk.v_1 = [pk.v_1.clone(), vec![Scalar::zero(); len - old_len]].concat();
        pk.vk.z = [pk.vk.z.clone(), vec![Scalar::zero(); len - old_len]].concat();

        let vk = &pk.vk;

        let mut t_1 = vec![];
        let mut t_minus1 = vec![];

        transcript.inner_product_domain_separator();




        let (h, _t_pprime, v_1, v_2, rho_prime) = IPSPInnerProductProof::folding_prover(
            transcript,
            &pk,
            &mut t_1,
            &mut t_minus1,
            &gens_f,
            &h,
            u,
        );

        debug_assert_eq!(
            _t_pprime,
            h * v_1 + gens_f * (v_1 * v_2) + u * rho_prime
        );

        let y_1 = Scalar::from_bits(rand256());
        let y_2 = Scalar::from_bits(rand256());


        let w = h * y_1 + gens_f * (y_1*v_2) + u * y_2;

        transcript.append_point(b"w", &w.compress());
        let c = transcript.challenge_scalar(b"c");

        let e_1 = y_1 - c * v_1;
        let e_2 = y_2 - c * rho_prime;

        debug_assert_eq!(
            w,
            _t_pprime * c+ h * e_1 + gens_f * (v_2 * e_1) + u * e_2
        );

        Self {
            w: w.compress(),
            e_1,
            e_2,
            t_1,
            t_minus1,
        }
    }

    /**
     * Verifies the given inner product proof.
     *
     * # Remarks
     * If valid, returns nothing. If invalid, returns an error indicating
     * that either the proof is malformed or invalid.
     */
    pub fn verify(
        &self,
        transcript: &mut Transcript,
        vk: &IPSPVerifierKnowledge,
        gens_f: &RistrettoPoint,
        h: &[RistrettoPoint],
        u: &RistrettoPoint,
    ) -> Result<(), ProofError> {
        assert_eq!(vk.z.len(), h.len());

        let now = Instant::now();
        let total = now;

        let len = h.len().next_power_of_two();
        let old_len = h.len();

        // Extend g and h to a power of 2.
        let vk = vk.clone();
        let h = [h, &vec![RistrettoPoint::default(); len - old_len]].concat();

        transcript.inner_product_domain_separator();


        trace!("Prefold {}s", now.elapsed().as_secs_f64());

        let now = Instant::now();

        let (z, h, t_pprime) = self.folding_verifier(transcript, &vk, &gens_f, &h, &vk.z)?;

        trace!("Fold {}s", now.elapsed().as_secs_f64());

        let now = Instant::now();

        transcript.append_point(b"w", &self.w);
        let c = transcript.challenge_scalar(b"c");
        let c_inv = c.invert();

        let w = self.w.decompress().ok_or(ProofError::MalformedProof)?;

        let lhs = w;
        let rhs = t_pprime * c + h * self.e_1 + gens_f * (self.e_1 * z) + u * self.e_2;

        trace!("Post fold {}s", now.elapsed().as_secs_f64());
        trace!("Verify time {}s", total.elapsed().as_secs_f64());

        if lhs == rhs {
            Ok(())
        } else {
            Err(ProofError::VerificationError)
        }
    }

    fn mad_scalar_point(
        v_1: &[RistrettoPoint],
        v_2: &[RistrettoPoint],
        c: Scalar,
    ) -> Vec<RistrettoPoint> {
        let v_1 = RistrettoPointVec::new(v_1);
        let v_2 = RistrettoPointVec::new(v_2);

        (v_1 + v_2 * c).into_iter().collect()
    }

    fn mad_mad_scalar_point(
        v_1: &[RistrettoPoint],
        v_2: &[RistrettoPoint],
        c: Scalar,
        c_inv: Scalar,
    ) -> Vec<RistrettoPoint> {
        let v_1 = RistrettoPointVec::new(v_1);
        let v_2 = RistrettoPointVec::new(v_2);

        (v_1 * c + v_2 * c_inv).into_iter().collect()
    }

    fn mad_mad_scalar_scalar(
        v_1: &[Scalar],
        v_2: &[Scalar],
        c: Scalar,
        c_inv: Scalar,
    ) -> Vec<Scalar> {
        // 1. check length
        assert_eq!(v_1.len(), v_2.len(), "Vectors v_1 and v_2 must have the same length");

        // 2. res = (v1 * c) + (v2 * c_inv)
        v_1.iter()
            .zip(v_2.iter())
            .map(|(s1, s2)| {
                (s1 * c) + (s2 * c_inv)
            })
            .collect()
    }

    #[allow(clippy::too_many_arguments)]
    /**
     * This a single iteration of the folding algorithm run by both
     * the prover and verifier.
     *
     * # Remarks
     * It
     * * Creates a challenge point `c`.
     * * Reduces `vec_z` and `h` from length `n` to length `n/2`
     * * Computes an updated `t''`.
     * * Returns (`z'`, `h'`, `t''`, `c`, `c_inv`)
     */
    fn fold_verifier(
        transcript: &mut Transcript,
        t: &RistrettoPoint,
        t_1: &RistrettoPoint,
        t_minus1: &RistrettoPoint,
        h_t: &[RistrettoPoint],
        h_b: &[RistrettoPoint],
        v_z_t: &[Scalar],
        v_z_b: &[Scalar],
    ) -> (
        Vec<RistrettoPoint>,
        Vec<Scalar>,
        RistrettoPoint,
        Scalar,
        Scalar,
    ) {
        debug_assert!(h_t.len() == h_b.len());
        debug_assert!(v_z_t.len() == h_b.len());

        transcript.append_point(b"t-1", &t_minus1.compress());
        transcript.append_point(b"t1", &t_1.compress());

        let c = transcript.challenge_scalar(b"c");
        let c_inv = c.invert();

        let h = Self::mad_mad_scalar_point(h_t, h_b, c_inv, c);
        let vec_z = Self::mad_mad_scalar_scalar(v_z_t, v_z_b, c_inv, c);
        let t = t_minus1 * c_inv * c_inv + t + t_1 * c * c;

        (h, vec_z, t, c, c_inv)
    }

    /**
     * The full folding algorithm for the verifier.
     */
    pub fn folding_verifier(
        &self,
        transcript: &mut Transcript,
        vk: &IPSPVerifierKnowledge,
        gens_f: &RistrettoPoint,
        h: &[RistrettoPoint],
        vec_z: &[Scalar],
    ) -> Result<(Scalar, RistrettoPoint, RistrettoPoint), ProofError> {
        let mut t = vk.t;

        if self.t_1.len() != self.t_minus1.len() {
            return Err(ProofError::MalformedProof);
        }

        if 0x1 << self.t_1.len() != h.len() {
            return Err(ProofError::MalformedProof);
        }

        let n = h.len();

        let mut c = vec![];

        // See Bulletproofs paper section 3.1 for what this optimization is. We're deferring
        // folding our generators g and h and instead computing factors s from each of the
        // challenge scalars.
        //
        // This allows us to compute a single MSM at the end to compute g and h rather than
        // performing SM folding.
        for (t_1, t_minus1) in self.t_1.iter().zip(self.t_minus1.iter()) {
            transcript.append_point(b"t-1", t_minus1);
            transcript.append_point(b"t1", t_1);

            c.push(transcript.challenge_scalar(b"c"));
        }

        let s_i = |i| {
            c.iter().rev().enumerate().fold(Scalar::one(), |p, (j, x)| {
                if i & (0x1 << j) != 0 {
                    p * x
                } else {
                    p * x.invert()
                }
            })
        };

        for ((t_1, t_minus_1), c) in self.t_1.iter().zip(self.t_minus1.iter()).zip(c.iter()) {
            let c_inv = c.invert();
            let t_1 = t_1.decompress().ok_or(ProofError::MalformedProof)?;
            let t_minus_1 = t_minus_1.decompress().ok_or(ProofError::MalformedProof)?;

            t = t_minus_1 * c_inv * c_inv + t + t_1 * c * c;
        }

        let s = (0..n).into_par_iter().map(s_i).collect::<Vec<_>>();
        let s_inv = ScalarVec::new(&s).invert().into_iter().collect::<Vec<_>>();
        let now = Instant::now();
        let h = parallel_multiscalar_multiplication(&s, h);
        let len = vec_z.len().next_power_of_two();
        let old_len = vec_z.len();
        let padded_z: Vec<Scalar> = [vec_z, &vec![Scalar::zero(); len - old_len]].concat();
        let z = padded_z.inner_product(s);
        trace!(
            "MSM {}s: {} SM/s",
            now.elapsed().as_secs_f64(),
            (2. * n as f64) / now.elapsed().as_secs_f64()
        );

        Ok((z, h, t))
    }

        /**
     * The full folding algorithm for the verifier.
     */
    pub fn folding_verifier_for_commits(
        &self,
        transcript: &mut Transcript,
        vk: &IPSPVerifierKnowledge,
        a: &RistrettoPoint,
        g: &[RistrettoPoint],
        h: &[RistrettoPoint],
    ) -> Result<(RistrettoPoint, RistrettoPoint, RistrettoPoint), ProofError> {
        let mut t = vk.t.clone();

        if self.t_1.len() != self.t_minus1.len() {
            return Err(ProofError::MalformedProof);
        }

        if 0x1 << self.t_1.len() != g.len() {
            return Err(ProofError::MalformedProof);
        }

        let n = g.len();

        let mut c = vec![];

        // See Bulletproofs paper section 3.1 for what this optimization is. We're deferring
        // folding our generators g and h and instead computing factors s from each of the
        // challenge scalars.
        //
        // This allows us to compute a single MSM at the end to compute g and h rather than
        // performing SM folding.
        for (t_1, t_minus1) in self.t_1.iter().zip(self.t_minus1.iter()) {
            transcript.append_point(b"t-1", t_minus1);
            transcript.append_point(b"t1", t_1);

            c.push(transcript.challenge_scalar(b"c"));
        }

        let s_i = |i| {
            c.iter().rev().enumerate().fold(Scalar::one(), |p, (j, x)| {
                if i & (0x1 << j) != 0 {
                    p * x
                } else {
                    p
                }
            })
        };

        for ((t_1, t_minus_1), c) in self.t_1.iter().zip(self.t_minus1.iter()).zip(c.iter()) {
            let c_inv = c.invert();
            let t_1 = t_1.decompress().ok_or(ProofError::MalformedProof)?;
            let t_minus_1 = t_minus_1.decompress().ok_or(ProofError::MalformedProof)?;

            t = t_minus_1 * c_inv + t + t_1 * c;
        }

        let s = (0..n).into_par_iter().map(s_i).collect::<Vec<_>>();
        let s_inv = ScalarVec::new(&s).invert().into_iter().collect::<Vec<_>>();
        let now = Instant::now();
        let g = parallel_multiscalar_multiplication(&s, g);
        let h = parallel_multiscalar_multiplication(&s_inv, h);
        trace!(
            "MSM {}s: {} SM/s",
            now.elapsed().as_secs_f64(),
            (2. * n as f64) / now.elapsed().as_secs_f64()
        );

        Ok((g, h, t))
    }

    #[allow(clippy::too_many_arguments)]
    /**
     * The full folding algorithm for the prover.
     */
    pub fn folding_prover(
        transcript: &mut Transcript,
        pk: &IPSPProverKnowledge,
        t_1_vec: &mut Vec<CompressedRistretto>,
        t_minus1_vec: &mut Vec<CompressedRistretto>,
        gens_f: &RistrettoPoint,
        h: &[RistrettoPoint],
        u: &RistrettoPoint,
    ) -> (
        RistrettoPoint,
        RistrettoPoint,
        Scalar,
        Scalar,
        Scalar,
    ) {
        let mut v_1 = pk.v_1.to_owned();
        let mut vec_z = pk.vk.z.to_owned();
        let mut h = h.to_owned();
        let mut t = pk.vk.t;

        let mut rho = pk.rho;

        loop {
            if v_1.len() == 1 {
                return (h[0], t, v_1[0], vec_z[0], rho);
            }

            let n_2 = v_1.len() / 2;

            // Split g, h, v_1, v_2 into top and bottom slices
            // (_t and _b respectively)
            let (h_t, h_b) = h.split_at(n_2);
            let (v_1_t, v_1_b) = v_1.split_at(n_2);
            let (v_z_t, v_z_b) = vec_z.split_at(n_2);

            // Sample random sigma_1 and sigma_-1
            let sigma = Scalar::from_bits(rand256());
            let sigma_minus1 = Scalar::from_bits(rand256());

            let x_minus1 = v_1_b.inner_product(v_z_t);
            let x = v_1_t.inner_product(v_z_b);

            let t_minus1 = parallel_multiscalar_multiplication(
                &v_1_b
                    .iter()
                    .chain([x_minus1].iter())
                    .chain([sigma_minus1].iter())
                    .cloned()
                    .collect::<Vec<Scalar>>(),
                &h_t.iter()
                    .chain([*gens_f].iter())
                    .chain([*u].iter())
                    .cloned()
                    .collect::<Vec<RistrettoPoint>>(),
            );

            let t_1 = parallel_multiscalar_multiplication(
                &v_1_t
                    .iter()
                    .chain([x].iter())
                    .chain([sigma].iter())
                    .cloned()
                    .collect::<Vec<Scalar>>(),
                &h_b.iter()
                    .chain([*gens_f].iter())
                    .chain([*u].iter())
                    .cloned()
                    .collect::<Vec<RistrettoPoint>>(),
            );

            let c;
            let c_inv;

            debug_assert!(h.len() > 1);

            // Both the prover and verifier need to collapse g, h and compute
            // new t.
            (h, vec_z, t, c, c_inv) =
                Self::fold_verifier(transcript, &t, &t_1, &t_minus1, h_t, h_b, v_z_t,v_z_b);

            let mad = |x: &[Scalar], y: &[Scalar], z_1: Scalar, z_2: Scalar| {
                x.iter().zip(y.iter()).map(|(a, b)| a * z_1 + b * z_2).collect()
            };

            // Prover needs to collapse vectors and update rho.
            v_1 = mad(v_1_t, v_1_b, c,c_inv);
            rho = rho + c_inv*c_inv*sigma_minus1 + c * c* sigma;

            t_1_vec.push(t_1.compress());
            t_minus1_vec.push(t_minus1.compress());
        }
    }
}
