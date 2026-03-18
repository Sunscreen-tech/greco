// Greco BFV Public Key Encryption Circuit
// Proves well-formedness of a BFV public-key ciphertext.
//
// Based on Section 5 of the Greco paper (https://eprint.iacr.org/2024/594)
// and adapted from the existing sk_encryption_circuit.rs in this codebase.
//
// Original Greco code: Copyright (c) 2024 Gaussian, MIT License

use crate::constants::pk_enc_constants_2048_1x53_2::{
    E0_BOUND, E1_BOUND, K0IS, K1_BOUND, N, P1_BOUNDS, P2_BOUNDS, QIS, R1_BOUNDS, R2_BOUNDS,
    U_BOUND,
};
use crate::poly::{Poly, PolyAssigned};
use axiom_eth::rlc::{
    chip::RlcChip,
    circuit::{
        builder::RlcCircuitBuilder, instructions::RlcCircuitInstructions, RlcCircuitParams,
    },
};
use halo2_base::{
    gates::{circuit::BaseCircuitParams, GateInstructions, RangeChip, RangeInstructions},
    utils::ScalarField,
    QuantumCell::Constant,
};
use serde::Deserialize;

/// Helper function to define test parameters for the PK encryption circuit.
/// Uses k=22 (larger than SK's k=21) due to approximately 2x the constraints.
pub fn pk_test_params() -> RlcCircuitParams {
    RlcCircuitParams {
        base: BaseCircuitParams {
            k: 22,
            num_advice_per_phase: vec![1, 1],
            num_fixed: 1,
            num_lookup_advice_per_phase: vec![0, 1],
            lookup_bits: Some(8),
            num_instance_columns: 1,
        },
        num_rlc_columns: 1,
    }
}

/// `BfvPkEncryptionCircuit` is a circuit that checks the correct formation of a
/// ciphertext resulting from BFV public key encryption.
///
/// The circuit enforces two constraint equations per CRT basis:
///
/// **Equation 1 (ct0):**
/// `ct0i = pk0i * u + e0 + k1 * k0i + r1i * qi + r2i * (X^N + 1)`
///
/// **Equation 2 (ct1):**
/// `ct1i = pk1i * u + e1 + p1i * qi + p2i * (X^N + 1)`
///
/// All polynomial coefficients and scalars are normalized to `[0, p)` where p is
/// the modulus of the BN254 scalar field.
///
/// # Parameters (Private Witnesses):
/// * `u`: binary randomness polynomial, sampled from {0, 1} (satisfies ternary bound).
/// * `e0`: error polynomial for ct0, sampled from discrete Gaussian.
/// * `e1`: error polynomial for ct1, sampled from discrete Gaussian.
/// * `k1`: scaled message polynomial.
/// * `r1is`: quotient polynomials for Equation 1 (ring reduction), per CRT basis.
/// * `r2is`: quotient polynomials for Equation 1 (cyclotomic reduction), per CRT basis.
/// * `p1is`: quotient polynomials for Equation 2 (ring reduction), per CRT basis.
/// * `p2is`: quotient polynomials for Equation 2 (cyclotomic reduction), per CRT basis.
///
/// # Parameters (Public Inputs):
/// * `pk0is`: public key component 0 per CRT basis.
/// * `pk1is`: public key component 1 per CRT basis.
/// * `ct0is`: ciphertext component 0 per CRT basis.
/// * `ct1is`: ciphertext component 1 per CRT basis.
#[derive(Deserialize, Clone)]
pub struct BfvPkEncryptionCircuit {
    // Private witnesses
    u: Vec<String>,
    e0: Vec<String>,
    e1: Vec<String>,
    k1: Vec<String>,
    r1is: Vec<Vec<String>>,
    r2is: Vec<Vec<String>>,
    p1is: Vec<Vec<String>>,
    p2is: Vec<Vec<String>>,
    // Public inputs
    pk0is: Vec<Vec<String>>,
    pk1is: Vec<Vec<String>>,
    ct0is: Vec<Vec<String>>,
    ct1is: Vec<Vec<String>>,
}

/// Payload returned by Phase 0 to be reused in Phase 1.
pub struct PkPayload<F: ScalarField> {
    u_assigned: PolyAssigned<F>,
    e0_assigned: PolyAssigned<F>,
    e1_assigned: PolyAssigned<F>,
    k1_assigned: PolyAssigned<F>,
    r1is_assigned: Vec<PolyAssigned<F>>,
    r2is_assigned: Vec<PolyAssigned<F>>,
    p1is_assigned: Vec<PolyAssigned<F>>,
    p2is_assigned: Vec<PolyAssigned<F>>,
    pk0is_assigned: Vec<PolyAssigned<F>>,
    pk1is_assigned: Vec<PolyAssigned<F>>,
    ct0is_assigned: Vec<PolyAssigned<F>>,
    ct1is_assigned: Vec<PolyAssigned<F>>,
}

impl<F: ScalarField> RlcCircuitInstructions<F> for BfvPkEncryptionCircuit {
    type FirstPhasePayload = PkPayload<F>;

    /// #### Phase 0
    ///
    /// Assigns all polynomials to the circuit witness table and exposes public inputs.
    /// At the end, the witness is committed and the commitment hash is used as the
    /// random challenge γ in Phase 1.
    fn virtual_assign_phase0(
        &self,
        builder: &mut RlcCircuitBuilder<F>,
        _: &RangeChip<F>,
    ) -> Self::FirstPhasePayload {
        let ctx = builder.base.main(0);
        let mut public_inputs = vec![];

        // Assign private witnesses (shared across all CRT bases)
        let u_assigned = PolyAssigned::new(ctx, Poly::<F>::new(self.u.clone()));
        let e0_assigned = PolyAssigned::new(ctx, Poly::<F>::new(self.e0.clone()));
        let e1_assigned = PolyAssigned::new(ctx, Poly::<F>::new(self.e1.clone()));
        let k1_assigned = PolyAssigned::new(ctx, Poly::<F>::new(self.k1.clone()));

        // Assign per-CRT-basis polynomials
        let mut r1is_assigned = vec![];
        let mut r2is_assigned = vec![];
        let mut p1is_assigned = vec![];
        let mut p2is_assigned = vec![];
        let mut pk0is_assigned = vec![];
        let mut pk1is_assigned = vec![];
        let mut ct0is_assigned = vec![];
        let mut ct1is_assigned = vec![];

        for z in 0..self.ct0is.len() {
            r1is_assigned.push(PolyAssigned::new(
                ctx,
                Poly::<F>::new(self.r1is[z].clone()),
            ));
            r2is_assigned.push(PolyAssigned::new(
                ctx,
                Poly::<F>::new(self.r2is[z].clone()),
            ));
            p1is_assigned.push(PolyAssigned::new(
                ctx,
                Poly::<F>::new(self.p1is[z].clone()),
            ));
            p2is_assigned.push(PolyAssigned::new(
                ctx,
                Poly::<F>::new(self.p2is[z].clone()),
            ));
            pk0is_assigned.push(PolyAssigned::new(
                ctx,
                Poly::<F>::new(self.pk0is[z].clone()),
            ));
            pk1is_assigned.push(PolyAssigned::new(
                ctx,
                Poly::<F>::new(self.pk1is[z].clone()),
            ));
            ct0is_assigned.push(PolyAssigned::new(
                ctx,
                Poly::<F>::new(self.ct0is[z].clone()),
            ));
            ct1is_assigned.push(PolyAssigned::new(
                ctx,
                Poly::<F>::new(self.ct1is[z].clone()),
            ));
        }

        // Expose public inputs: pk0is, pk1is, ct0is, ct1is
        for pk0i in pk0is_assigned.iter() {
            for coeff in &pk0i.assigned_coefficients {
                public_inputs.push(*coeff);
            }
        }
        for pk1i in pk1is_assigned.iter() {
            for coeff in &pk1i.assigned_coefficients {
                public_inputs.push(*coeff);
            }
        }
        for ct0i in ct0is_assigned.iter() {
            for coeff in &ct0i.assigned_coefficients {
                public_inputs.push(*coeff);
            }
        }
        for ct1i in ct1is_assigned.iter() {
            for coeff in &ct1i.assigned_coefficients {
                public_inputs.push(*coeff);
            }
        }

        builder.base.assigned_instances[0] = public_inputs;

        PkPayload {
            u_assigned,
            e0_assigned,
            e1_assigned,
            k1_assigned,
            r1is_assigned,
            r2is_assigned,
            p1is_assigned,
            p2is_assigned,
            pk0is_assigned,
            pk1is_assigned,
            ct0is_assigned,
            ct1is_assigned,
        }
    }

    /// #### Phase 1
    ///
    /// Enforces three categories of constraints:
    ///
    /// 1. **Range checks** on private polynomial coefficients
    /// 2. **Schwartz-Zippel evaluation** of all polynomials at random challenge γ
    /// 3. **Correct encryption constraints** (two equations per CRT basis)
    fn virtual_assign_phase1(
        builder: &mut RlcCircuitBuilder<F>,
        range: &RangeChip<F>,
        rlc: &RlcChip<F>,
        payload: Self::FirstPhasePayload,
    ) {
        let PkPayload {
            u_assigned,
            e0_assigned,
            e1_assigned,
            k1_assigned,
            r1is_assigned,
            r2is_assigned,
            p1is_assigned,
            p2is_assigned,
            pk0is_assigned,
            pk1is_assigned,
            ct0is_assigned,
            ct1is_assigned,
        } = payload;

        let (ctx_gate, ctx_rlc) = builder.rlc_ctx_pair();
        let gate = range.gate();

        // Precompute circuit constants for each CRT basis
        let mut qi_constants = vec![];
        let mut k0i_constants = vec![];
        for z in 0..ct0is_assigned.len() {
            qi_constants.push(Constant(F::from_str_vartime(QIS[z]).unwrap()));
            k0i_constants.push(Constant(F::from_str_vartime(K0IS[z]).unwrap()));
        }

        // ---- RANGE CHECKS ----

        // Range check shared private witnesses
        u_assigned.range_check(ctx_gate, range, U_BOUND);
        e0_assigned.range_check(ctx_gate, range, E0_BOUND);
        e1_assigned.range_check(ctx_gate, range, E1_BOUND);
        k1_assigned.range_check(ctx_gate, range, K1_BOUND);

        // Range check per-CRT-basis private witnesses
        for z in 0..ct0is_assigned.len() {
            r1is_assigned[z].range_check(ctx_gate, range, R1_BOUNDS[z]);
            r2is_assigned[z].range_check(ctx_gate, range, R2_BOUNDS[z]);
            p1is_assigned[z].range_check(ctx_gate, range, P1_BOUNDS[z]);
            p2is_assigned[z].range_check(ctx_gate, range, P2_BOUNDS[z]);
        }

        // ---- EVALUATION AT γ ----

        // Compute γ^N + 1 (cyclotomic polynomial evaluated at γ)
        let bits_used = usize::BITS as usize - N.leading_zeros() as usize;
        rlc.load_rlc_cache((ctx_gate, ctx_rlc), gate, bits_used);
        let cyclo_at_gamma = rlc.rlc_pow_fixed(ctx_gate, gate, N);
        let cyclo_at_gamma = gate.add(ctx_gate, cyclo_at_gamma, Constant(F::from(1)));

        // Evaluate shared polynomials at γ (done once)
        let u_at_gamma = u_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);
        let e0_at_gamma = e0_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);
        let e1_at_gamma = e1_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);
        let k1_at_gamma = k1_assigned.enforce_eval_at_gamma(ctx_rlc, rlc);

        // ---- CORRECT ENCRYPTION CONSTRAINTS (per CRT basis) ----

        for z in 0..ct0is_assigned.len() {
            // Evaluate per-CRT polynomials at γ
            let r1i_at_gamma = r1is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let r2i_at_gamma = r2is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let p1i_at_gamma = p1is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let p2i_at_gamma = p2is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let pk0i_at_gamma = pk0is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let pk1i_at_gamma = pk1is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let ct0i_at_gamma = ct0is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);
            let ct1i_at_gamma = ct1is_assigned[z].enforce_eval_at_gamma(ctx_rlc, rlc);

            // ---- EQUATION 1: ct0i(γ) = pk0i(γ)*u(γ) + e0(γ) + k1(γ)*k0i + r1i(γ)*qi + r2i(γ)*cyclo(γ) ----

            // rhs1 = pk0i(γ) * u(γ) + e0(γ)
            let rhs1 = gate.mul_add(ctx_gate, pk0i_at_gamma, u_at_gamma, e0_at_gamma);
            // rhs1 += k1(γ) * k0i
            let rhs1 = gate.mul_add(ctx_gate, k1_at_gamma, k0i_constants[z], rhs1);
            // rhs1 += r1i(γ) * qi
            let rhs1 = gate.mul_add(ctx_gate, r1i_at_gamma, qi_constants[z], rhs1);
            // rhs1 += r2i(γ) * cyclo(γ)
            let rhs1 = gate.mul_add(ctx_gate, r2i_at_gamma, cyclo_at_gamma, rhs1);

            // Assert ct0i(γ) == rhs1
            let res1 = gate.is_equal(ctx_gate, ct0i_at_gamma, rhs1);
            gate.assert_is_const(ctx_gate, &res1, &F::from(1));

            // ---- EQUATION 2: ct1i(γ) = pk1i(γ)*u(γ) + e1(γ) + p1i(γ)*qi + p2i(γ)*cyclo(γ) ----

            // rhs2 = pk1i(γ) * u(γ) + e1(γ)
            let rhs2 = gate.mul_add(ctx_gate, pk1i_at_gamma, u_at_gamma, e1_at_gamma);
            // rhs2 += p1i(γ) * qi
            let rhs2 = gate.mul_add(ctx_gate, p1i_at_gamma, qi_constants[z], rhs2);
            // rhs2 += p2i(γ) * cyclo(γ)
            let rhs2 = gate.mul_add(ctx_gate, p2i_at_gamma, cyclo_at_gamma, rhs2);

            // Assert ct1i(γ) == rhs2
            let res2 = gate.is_equal(ctx_gate, ct1i_at_gamma, rhs2);
            gate.assert_is_const(ctx_gate, &res2, &F::from(1));
        }
    }

    fn instances(&self) -> Vec<Vec<F>> {
        let mut instance = vec![];
        for pk0i in self.pk0is.iter() {
            instance.extend(Poly::<F>::new(pk0i.clone()).coefficients);
        }
        for pk1i in self.pk1is.iter() {
            instance.extend(Poly::<F>::new(pk1i.clone()).coefficients);
        }
        for ct0i in self.ct0is.iter() {
            instance.extend(Poly::<F>::new(ct0i.clone()).coefficients);
        }
        for ct1i in self.ct1is.iter() {
            instance.extend(Poly::<F>::new(ct1i.clone()).coefficients);
        }
        vec![instance]
    }
}

#[cfg(test)]
mod test {
    use super::pk_test_params;
    use crate::{
        constants::pk_enc_constants_2048_1x53_2::{N, R1_BOUNDS},
        pk_encryption_circuit::BfvPkEncryptionCircuit,
    };
    use axiom_eth::rlc::{
        circuit::{builder::RlcCircuitBuilder, instructions::RlcCircuitInstructions},
        utils::executor::RlcExecutor,
    };
    use halo2_base::{
        gates::circuit::CircuitBuilderStage,
        halo2_proofs::{
            dev::MockProver,
            halo2curves::bn256::Fr,
            plonk::{keygen_pk, keygen_vk},
        },
        utils::{
            fs::gen_srs,
            testing::{check_proof_with_instances, gen_proof_with_instances},
        },
    };
    use std::{fs::File, io::Read};

    #[test]
    pub fn test_pk_enc_valid() {
        let file_path = "src/data/pk_enc_2048_1x53_2.json";
        let mut file = File::open(file_path).unwrap();
        let mut data = String::new();
        file.read_to_string(&mut data).unwrap();
        let pk_enc_circuit = serde_json::from_str::<BfvPkEncryptionCircuit>(&data).unwrap();

        let rlc_circuit_params = pk_test_params();
        let mut mock_builder: RlcCircuitBuilder<Fr> =
            RlcCircuitBuilder::from_stage(CircuitBuilderStage::Mock, 0)
                .use_params(rlc_circuit_params.clone());
        mock_builder.base.set_lookup_bits(8);

        let instances = pk_enc_circuit.instances();
        let rlc_circuit = RlcExecutor::new(mock_builder, pk_enc_circuit);

        MockProver::run(
            rlc_circuit_params.base.k.try_into().unwrap(),
            &rlc_circuit,
            instances,
        )
        .unwrap()
        .assert_satisfied();
    }

    #[test]
    pub fn test_pk_enc_invalid_range() {
        let file_path = "src/data/pk_enc_2048_1x53_2.json";
        let mut file = File::open(file_path).unwrap();
        let mut data = String::new();
        file.read_to_string(&mut data).unwrap();
        let mut pk_enc_circuit = serde_json::from_str::<BfvPkEncryptionCircuit>(&data).unwrap();

        // Invalidate: set the first coefficient of r1is[0] to one above its bound.
        // This should cause the range check to fail in Phase 1 and the equality
        // constraint to fail for the 0th CRT basis.
        let out_of_range_coeff = R1_BOUNDS[0] + 1;
        pk_enc_circuit.r1is[0][0] = out_of_range_coeff.to_string();

        let rlc_circuit_params = pk_test_params();
        let mut mock_builder: RlcCircuitBuilder<Fr> =
            RlcCircuitBuilder::from_stage(CircuitBuilderStage::Mock, 0)
                .use_params(rlc_circuit_params.clone());
        mock_builder.base.set_lookup_bits(8);

        let instances = pk_enc_circuit.instances();
        let rlc_circuit = RlcExecutor::new(mock_builder, pk_enc_circuit);

        let invalid_mock_prover = MockProver::run(
            rlc_circuit_params.base.k.try_into().unwrap(),
            &rlc_circuit,
            instances,
        )
        .unwrap();

        assert!(invalid_mock_prover.verify().is_err());
    }

    #[test]
    pub fn test_pk_enc_invalid_polys() {
        let file_path = "src/data/pk_enc_2048_1x53_2.json";
        let mut file = File::open(file_path).unwrap();
        let mut data = String::new();
        file.read_to_string(&mut data).unwrap();
        let mut pk_enc_circuit = serde_json::from_str::<BfvPkEncryptionCircuit>(&data).unwrap();

        // Invalidate: replace u with a wrong polynomial (all-ones — valid ternary bound,
        // but not the u used to produce ct0/ct1).  The equality constraints for both
        // equations should fail.
        pk_enc_circuit.u = vec!["1".to_string(); N];

        let rlc_circuit_params = pk_test_params();
        let mut mock_builder: RlcCircuitBuilder<Fr> =
            RlcCircuitBuilder::from_stage(CircuitBuilderStage::Mock, 0)
                .use_params(rlc_circuit_params.clone());
        mock_builder.base.set_lookup_bits(8);

        let instances = pk_enc_circuit.instances();
        let rlc_circuit = RlcExecutor::new(mock_builder, pk_enc_circuit);

        let invalid_mock_prover = MockProver::run(
            rlc_circuit_params.base.k.try_into().unwrap(),
            &rlc_circuit,
            instances,
        )
        .unwrap();

        assert!(invalid_mock_prover.verify().is_err());
    }

    #[test]
    pub fn test_pk_enc_invalid_eq2() {
        // This test specifically targets Equation 2:
        //   ct1i = pk1i*u + e1 + p1i*qi + p2i*cyclo
        //
        // By replacing e1 with wrong values (all-ones — within the Gaussian bound,
        // so the range check still passes) while keeping u, e0, k1, r1is, r2is
        // unchanged, Equation 1 remains satisfied and only Equation 2 fails.
        // This gives independent assurance that the p1i/p2i constraint path is
        // actually enforced and cannot be bypassed.
        let file_path = "src/data/pk_enc_2048_1x53_2.json";
        let mut file = File::open(file_path).unwrap();
        let mut data = String::new();
        file.read_to_string(&mut data).unwrap();
        let mut pk_enc_circuit = serde_json::from_str::<BfvPkEncryptionCircuit>(&data).unwrap();

        // All-ones e1: valid for range check (1 << E1_BOUND) but wrong for ct1.
        pk_enc_circuit.e1 = vec!["1".to_string(); N];

        let rlc_circuit_params = pk_test_params();
        let mut mock_builder: RlcCircuitBuilder<Fr> =
            RlcCircuitBuilder::from_stage(CircuitBuilderStage::Mock, 0)
                .use_params(rlc_circuit_params.clone());
        mock_builder.base.set_lookup_bits(8);

        let instances = pk_enc_circuit.instances();
        let rlc_circuit = RlcExecutor::new(mock_builder, pk_enc_circuit);

        let invalid_mock_prover = MockProver::run(
            rlc_circuit_params.base.k.try_into().unwrap(),
            &rlc_circuit,
            instances,
        )
        .unwrap();

        assert!(invalid_mock_prover.verify().is_err());
    }

    #[test]
    pub fn test_pk_enc_full_prover() {
        let file_path_zeroes = "src/data/pk_enc_2048_1x53_2_zeroes.json";
        let mut file = File::open(file_path_zeroes).unwrap();
        let mut data = String::new();
        file.read_to_string(&mut data).unwrap();
        let empty_pk_enc_circuit =
            serde_json::from_str::<BfvPkEncryptionCircuit>(&data).unwrap();

        let k = 16;
        let kzg_params = gen_srs(k as u32);

        let mut key_gen_builder =
            RlcCircuitBuilder::from_stage(CircuitBuilderStage::Keygen, 0).use_k(k);
        key_gen_builder.base.set_lookup_bits(k - 1);
        key_gen_builder.base.set_instance_columns(1);

        let rlc_circuit = RlcExecutor::new(key_gen_builder, empty_pk_enc_circuit.clone());
        let rlc_circuit_params = rlc_circuit.0.calculate_params(Some(9));

        let vk = keygen_vk(&kzg_params, &rlc_circuit).unwrap();
        let pk = keygen_pk(&kzg_params, vk, &rlc_circuit).unwrap();
        let break_points = rlc_circuit.0.builder.borrow().break_points();
        drop(rlc_circuit);

        let proof_gen_builder: RlcCircuitBuilder<Fr> =
            RlcCircuitBuilder::from_stage(CircuitBuilderStage::Prover, 0)
                .use_params(rlc_circuit_params);

        let file_path = "src/data/pk_enc_2048_1x53_2.json";
        let mut file = File::open(file_path).unwrap();
        let mut data = String::new();
        file.read_to_string(&mut data).unwrap();
        let pk_enc_circuit = serde_json::from_str::<BfvPkEncryptionCircuit>(&data).unwrap();

        let instances = pk_enc_circuit.instances();
        let rlc_circuit = RlcExecutor::new(proof_gen_builder, pk_enc_circuit.clone());
        rlc_circuit
            .0
            .builder
            .borrow_mut()
            .set_break_points(break_points);

        let proof = gen_proof_with_instances(&kzg_params, &pk, rlc_circuit, &[&instances[0]]);
        check_proof_with_instances(&kzg_params, pk.get_vk(), &proof, &[&instances[0]], true);
    }
}
