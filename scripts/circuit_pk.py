"""
Generate Rust constants and JSON inputs for the BFV zk proof of PUBLIC KEY encryption circuit.

Adapted from the secret key encryption script (circuit_sk.py) and the deleted
circuit_pk.py (commit 79ea0b8) to produce witness data for the Halo2 PK circuit.

The PK circuit proves two constraint equations per CRT basis:
  Equation 1: ct0i = pk0i*u + e0 + k1*k0i + r1i*qi + r2i*(X^N+1)
  Equation 2: ct1i = pk1i*u + e1 + p1i*qi + p2i*(X^N+1)
"""

import os
import copy
import json
import argparse
from bfv.crt import CRTModuli
from bfv.bfv import BFVCrt
from bfv.discrete_gauss import DiscreteGaussian
from bfv.polynomial import Polynomial, poly_div
from random import randint
from utils import assign_to_circuit, count_advice_cells_needed_for_poly_range_check, print_advice_cells_info


def main(args):
    n = args.n
    qis = json.loads(args.qis)
    t = args.t

    crt_moduli = CRTModuli(qis)
    sigma = 3.2
    discrete_gaussian = DiscreteGaussian(sigma)
    bfv_crt = BFVCrt(crt_moduli, n, t, discrete_gaussian)

    # =========================================================================
    # ENCRYPTION PHASE - performed outside the circuit
    # =========================================================================

    # Generate secret key (ternary distribution)
    s = bfv_crt.SecretKeyGen()

    # Generate public key: pk = (pk0, pk1) for each CRT basis
    e_pk = bfv_crt.bfv_q.rlwe.SampleFromErrorDistribution()
    ais_pk = []
    for i in range(len(crt_moduli.qis)):
        ais_pk.append(bfv_crt.bfv_qis[i].rlwe.Rq.sample_polynomial())
    pub_keys = bfv_crt.PublicKeyGen(s, e_pk, ais_pk)

    # Sample plaintext message.
    # bfv-py's sample_polynomial uses centered bounds [-(t-1)/2, (t-1)/2], which
    # are non-integer for even t (e.g. t=2 gives [-0.5, 0.5]).  For even t we
    # sample binary {0,1} coefficients directly.
    if t % 2 == 1:
        m = bfv_crt.bfv_q.rlwe.Rt.sample_polynomial()
    else:
        m = Polynomial([randint(0, t - 1) for _ in range(n)])

    # Sample PK encryption randomness
    u = bfv_crt.bfv_q.rlwe.SampleFromTernaryDistribution()
    e0 = bfv_crt.bfv_q.rlwe.SampleFromErrorDistribution()
    e1 = bfv_crt.bfv_q.rlwe.SampleFromErrorDistribution()

    # Perform public key encryption manually (bfv-py PubKeyEncrypt has a bug
    # where pk1_u is double-wrapped in Polynomial())
    ciphertexts = []
    partial_scaled_message = m.scalar_mul(crt_moduli.q)
    partial_scaled_message.reduce_coefficients_by_modulus(t)

    for i, pk_qi in enumerate(pub_keys):
        neg_mod_inv_t = pow(-t, -1, qis[i])
        scaled_message = partial_scaled_message.scalar_mul(neg_mod_inv_t)

        pk0_u = pk_qi[0] * u
        ct_0 = scaled_message + pk0_u + e0
        ct_0.reduce_in_ring(bfv_crt.bfv_qis[i].rlwe.Rq)

        pk1_u = pk_qi[1] * u
        ct_1 = pk1_u + e1
        ct_1.reduce_in_ring(bfv_crt.bfv_qis[i].rlwe.Rq)

        ciphertexts.append((ct_0, ct_1))

    # Sanity check: decrypt and verify
    message_prime = bfv_crt.Decrypt(s, ciphertexts)
    assert m == message_prime, "Decryption failed!"

    # k1 = [Q*M]_t (scaled message polynomial)
    k1 = m.scalar_mul(crt_moduli.q)
    k1.reduce_coefficients_by_modulus(t)

    # BN254 scalar field modulus
    p = 21888242871839275222246405745257275088548364400416034343698204186575808495617

    cyclo = [1] + [0] * (n - 1) + [1]
    cyclo = Polynomial(cyclo)

    # Per-CRT-basis witness data
    r1is = []
    r2is = []
    p1is = []
    p2is = []
    k0is = []
    ct0is = []
    ct1is = []
    pk0is = []
    pk1is = []
    vis = []
    yis = []

    # =========================================================================
    # SETUP PHASE - compute r1, r2, p1, p2 for each CRT basis
    # =========================================================================

    for i, ciphertext in enumerate(ciphertexts):
        pk0i = pub_keys[i][0]
        pk1i = pub_keys[i][1]

        # k0i = -t^{-1} mod qi
        k0i = pow(-t, -1, qis[i])

        # --- Equation 1: ct0i = pk0i*u + e0 + k0i*k1 ---

        # vi = pk0i * u + e0 + k0i * k1 (unreduced, degree 2N-2)
        vi = pk0i * u + e0 + k1.scalar_mul(k0i)
        assert len(vi.coefficients) - 1 == 2 * n - 2

        ct0i = ciphertext[0]

        # Verify: vi reduced mod R_qi = ct0i
        vi_clone = copy.deepcopy(vi)
        vi_clone.reduce_coefficients_by_cyclo(cyclo.coefficients)
        vi_clone.reduce_coefficients_by_modulus(qis[i])
        assert vi_clone == ct0i

        # Compute r2i: (ct0i - vi) / cyclo mod Z_qi
        num = ct0i + vi.scalar_mul(-1)
        num.reduce_coefficients_by_modulus(qis[i])
        (quotient, rem) = poly_div(num.coefficients, cyclo.coefficients)
        assert rem == []
        r2i = Polynomial(quotient)
        assert len(r2i.coefficients) - 1 == n - 2

        # Compute r1i: (ct0i - vi - r2i*cyclo) / qi
        num = ct0i + vi.scalar_mul(-1) + (r2i * cyclo).scalar_mul(-1)
        (quotient, rem) = poly_div(num.coefficients, [qis[i]])
        assert rem == []
        r1i = Polynomial(quotient)

        # Verify: ct0i = vi + r1i*qi + r2i*cyclo
        lhs = ct0i
        rhs = vi + r1i.scalar_mul(qis[i]) + (r2i * cyclo)
        while len(rhs.coefficients) > n and rhs.coefficients[0] == 0:
            rhs.coefficients.pop(0)
        assert lhs == rhs

        # --- Equation 2: ct1i = pk1i*u + e1 ---

        # yi = pk1i * u + e1 (unreduced, degree 2N-2)
        yi = pk1i * u + e1
        assert len(yi.coefficients) - 1 == 2 * n - 2

        ct1i = ciphertext[1]

        # Verify: yi reduced mod R_qi = ct1i
        yi_clone = copy.deepcopy(yi)
        yi_clone.reduce_coefficients_by_cyclo(cyclo.coefficients)
        yi_clone.reduce_coefficients_by_modulus(qis[i])
        assert yi_clone == ct1i

        # Compute p2i: (ct1i - yi) / cyclo mod Z_qi
        num = ct1i + yi.scalar_mul(-1)
        num.reduce_coefficients_by_modulus(qis[i])
        (quotient, rem) = poly_div(num.coefficients, cyclo.coefficients)
        assert rem == []
        p2i = Polynomial(quotient)
        assert len(p2i.coefficients) - 1 == n - 2

        # Compute p1i: (ct1i - yi - p2i*cyclo) / qi
        num = ct1i + yi.scalar_mul(-1) + (p2i * cyclo).scalar_mul(-1)
        (quotient, rem) = poly_div(num.coefficients, [qis[i]])
        assert rem == []
        p1i = Polynomial(quotient)

        # Verify: ct1i = yi + p1i*qi + p2i*cyclo
        lhs = ct1i
        rhs = yi + p1i.scalar_mul(qis[i]) + (p2i * cyclo)
        while len(rhs.coefficients) > n and rhs.coefficients[0] == 0:
            rhs.coefficients.pop(0)
        assert lhs == rhs

        r1is.append(r1i)
        r2is.append(r2i)
        p1is.append(p1i)
        p2is.append(p2i)
        k0is.append(k0i)
        ct0is.append(ct0i)
        ct1is.append(ct1i)
        pk0is.append(pk0i)
        pk1is.append(pk1i)
        vis.append(vi)
        yis.append(yi)

    # =========================================================================
    # RANGE CHECK VERIFICATION & BOUNDS COMPUTATION
    # =========================================================================

    b = int(discrete_gaussian.z_upper)
    lookup_bits = 8

    # u bound (ternary: {-1, 0, 1})
    u_bound = 1
    assert all(coeff >= -u_bound and coeff <= u_bound for coeff in u.coefficients)

    # e0, e1 bounds (Gaussian)
    assert all(coeff >= -b and coeff <= b for coeff in e0.coefficients)
    assert all(coeff >= -b and coeff <= b for coeff in e1.coefficients)

    # k1 bound.
    # For odd t:  k1 coeffs in [-(t-1)/2, (t-1)/2], so bound = (t-1)//2.
    # For even t: k1 = [Q*m] mod t = m*1 mod t = m (since Q=qi is odd), so coeffs
    #             in {0,...,t-1}, bound = t//2 (covers {0,...,t-1} under [-t//2, t//2]).
    # The unified formula t//2 is correct for both parities:
    #   t=2     -> 1  (covers {0,1})
    #   t=65537 -> 32768  (covers {-32768,...,32768})
    k1_bound = t // 2
    assert all(coeff >= -k1_bound and coeff <= k1_bound for coeff in k1.coefficients)

    r1_bounds = []
    r2_bounds = []
    p1_bounds = []
    p2_bounds = []

    for i in range(len(ciphertexts)):
        # r2i bound: (qi-1)/2
        r2i_bound = int((qis[i] - 1) / 2)
        r2_bounds.append(r2i_bound)
        assert all(coeff >= -r2i_bound and coeff <= r2i_bound for coeff in r2is[i].coefficients)

        # r1i bound: floor(((N+2)*(qi-1)/2 + B + k1_bound * |k0i|) / qi)
        # Uses k1_bound (not (t-1)//2) so it is correct for both even and odd t.
        r1i_bound = int(((qis[i] - 1) // 2 * (n + 2) + b + k1_bound * abs(k0is[i])) / qis[i])
        r1_bounds.append(r1i_bound)
        assert all(coeff >= -r1i_bound and coeff <= r1i_bound for coeff in r1is[i].coefficients)

        # p2i bound: (qi-1)/2 (same as r2i)
        p2i_bound = int((qis[i] - 1) / 2)
        p2_bounds.append(p2i_bound)
        assert all(coeff >= -p2i_bound and coeff <= p2i_bound for coeff in p2is[i].coefficients)

        # p1i bound: floor(((N+2)*(qi-1)/2 + B) / qi) — no k1*k0i term
        p1i_bound = int(((qis[i] - 1) // 2 * (n + 2) + b) / qis[i])
        p1_bounds.append(p1i_bound)
        assert all(coeff >= -p1i_bound and coeff <= p1i_bound for coeff in p1is[i].coefficients)

        # vi bound: pk0i*u contributes N*(qi-1)/2 (N terms, each bounded by (qi-1)/2),
        # plus e0 (b) and k0i*k1 (k1_bound * |k0i|).
        vi_bound = int((qis[i] - 1) / 2) * n + b + k1_bound * abs(k0is[i])
        assert all(coeff >= -vi_bound and coeff <= vi_bound for coeff in vis[i].coefficients), \
            f"vi bound check failed for basis {i}"

        # yi bound: pk1i*u contributes N*(qi-1)/2, plus e1 (b).
        yi_bound = int((qis[i] - 1) / 2) * n + b
        assert all(coeff >= -yi_bound and coeff <= yi_bound for coeff in yis[i].coefficients), \
            f"yi bound check failed for basis {i}"

    # =========================================================================
    # CIRCUIT ASSIGNMENT (convert to field elements in Z_p)
    # =========================================================================

    # NOTE ON COEFFICIENT ORDER: bfv-py polynomials store coefficients in
    # DESCENDING order (highest degree first). assign_to_circuit() preserves
    # this order, so all JSON coefficient arrays below are also descending.
    # The Halo2 circuit uses Greco's Poly type which expects the same
    # descending convention — this must be maintained consistently.

    u_assigned = assign_to_circuit(u, p)
    # Verify: non-negative coefficients in [0, u_bound], negative mapped to [p-u_bound, p)
    assert all(
        (0 <= coeff <= u_bound) or (p - u_bound <= coeff < p)
        for coeff in u_assigned.coefficients
    ), "u field element assignment check failed"
    u_shifted = Polynomial([(coeff + u_bound) % p for coeff in u_assigned.coefficients])
    assert all(0 <= coeff <= 2 * u_bound for coeff in u_shifted.coefficients), \
        "u shifted polynomial check failed"

    e0_assigned = assign_to_circuit(e0, p)
    assert all(
        (0 <= coeff <= b) or (p - b <= coeff < p)
        for coeff in e0_assigned.coefficients
    ), "e0 field element assignment check failed"
    e0_shifted = Polynomial([(coeff + b) % p for coeff in e0_assigned.coefficients])
    assert all(0 <= coeff <= 2 * b for coeff in e0_shifted.coefficients), \
        "e0 shifted polynomial check failed"

    e1_assigned = assign_to_circuit(e1, p)
    assert all(
        (0 <= coeff <= b) or (p - b <= coeff < p)
        for coeff in e1_assigned.coefficients
    ), "e1 field element assignment check failed"
    e1_shifted = Polynomial([(coeff + b) % p for coeff in e1_assigned.coefficients])
    assert all(0 <= coeff <= 2 * b for coeff in e1_shifted.coefficients), \
        "e1 shifted polynomial check failed"

    k1_assigned = assign_to_circuit(k1, p)
    assert all(
        (0 <= coeff <= k1_bound) or (p - k1_bound <= coeff < p)
        for coeff in k1_assigned.coefficients
    ), "k1 field element assignment check failed"
    k1_shifted = Polynomial([(coeff + k1_bound) % p for coeff in k1_assigned.coefficients])
    assert all(0 <= coeff <= 2 * k1_bound for coeff in k1_shifted.coefficients), \
        "k1 shifted polynomial check failed"

    r1is_assigned = [assign_to_circuit(r1is[i], p) for i in range(len(ciphertexts))]
    r2is_assigned = [assign_to_circuit(r2is[i], p) for i in range(len(ciphertexts))]
    p1is_assigned = [assign_to_circuit(p1is[i], p) for i in range(len(ciphertexts))]
    p2is_assigned = [assign_to_circuit(p2is[i], p) for i in range(len(ciphertexts))]

    # Verify field element assignments for per-CRT-basis private polynomials
    for i in range(len(ciphertexts)):
        assert all(
            (0 <= coeff <= r1_bounds[i]) or (p - r1_bounds[i] <= coeff < p)
            for coeff in r1is_assigned[i].coefficients
        ), f"r1is[{i}] field element assignment check failed"
        r1i_shifted = Polynomial([(coeff + r1_bounds[i]) % p for coeff in r1is_assigned[i].coefficients])
        assert all(0 <= coeff <= 2 * r1_bounds[i] for coeff in r1i_shifted.coefficients), \
            f"r1is[{i}] shifted polynomial check failed"

        assert all(
            (0 <= coeff <= r2_bounds[i]) or (p - r2_bounds[i] <= coeff < p)
            for coeff in r2is_assigned[i].coefficients
        ), f"r2is[{i}] field element assignment check failed"
        r2i_shifted = Polynomial([(coeff + r2_bounds[i]) % p for coeff in r2is_assigned[i].coefficients])
        assert all(0 <= coeff <= 2 * r2_bounds[i] for coeff in r2i_shifted.coefficients), \
            f"r2is[{i}] shifted polynomial check failed"

        assert all(
            (0 <= coeff <= p1_bounds[i]) or (p - p1_bounds[i] <= coeff < p)
            for coeff in p1is_assigned[i].coefficients
        ), f"p1is[{i}] field element assignment check failed"
        p1i_shifted = Polynomial([(coeff + p1_bounds[i]) % p for coeff in p1is_assigned[i].coefficients])
        assert all(0 <= coeff <= 2 * p1_bounds[i] for coeff in p1i_shifted.coefficients), \
            f"p1is[{i}] shifted polynomial check failed"

        assert all(
            (0 <= coeff <= p2_bounds[i]) or (p - p2_bounds[i] <= coeff < p)
            for coeff in p2is_assigned[i].coefficients
        ), f"p2is[{i}] field element assignment check failed"
        p2i_shifted = Polynomial([(coeff + p2_bounds[i]) % p for coeff in p2is_assigned[i].coefficients])
        assert all(0 <= coeff <= 2 * p2_bounds[i] for coeff in p2i_shifted.coefficients), \
            f"p2is[{i}] shifted polynomial check failed"

    pk0is_in_p = [assign_to_circuit(pk0is[i], p) for i in range(len(ciphertexts))]
    pk1is_in_p = [assign_to_circuit(pk1is[i], p) for i in range(len(ciphertexts))]
    ct0is_in_p = [assign_to_circuit(ct0is[i], p) for i in range(len(ciphertexts))]
    ct1is_in_p = [assign_to_circuit(ct1is[i], p) for i in range(len(ciphertexts))]

    # Compute k0i constants in field
    k0i_constants = []
    qi_constants = []
    for i in range(len(ciphertexts)):
        k0i_constant = assign_to_circuit(Polynomial([k0is[i]]), p).coefficients[0]
        k0i_constants.append(k0i_constant)
        qi_constants.append(qis[i])

    # =========================================================================
    # CONSTRAINT VERIFICATION (sanity check before generating JSON)
    # =========================================================================

    gamma = randint(0, 1000)

    for i in range(len(ciphertexts)):
        # Verify Equation 1
        u_gamma = u_assigned.evaluate(gamma)
        e0_gamma = e0_assigned.evaluate(gamma)
        k1_gamma = k1_assigned.evaluate(gamma)
        r1i_gamma = r1is_assigned[i].evaluate(gamma)
        r2i_gamma = r2is_assigned[i].evaluate(gamma)
        pk0i_gamma = pk0is_in_p[i].evaluate(gamma)
        ct0i_gamma = ct0is_in_p[i].evaluate(gamma)
        cyclo_gamma = cyclo.evaluate(gamma)

        lhs = ct0i_gamma
        rhs = (pk0i_gamma * u_gamma + e0_gamma
               + k1_gamma * k0i_constants[i]
               + r1i_gamma * qi_constants[i]
               + r2i_gamma * cyclo_gamma)
        assert lhs % p == rhs % p, f"Equation 1 failed for CRT basis {i}"

        # Verify Equation 2
        e1_gamma = e1_assigned.evaluate(gamma)
        p1i_gamma = p1is_assigned[i].evaluate(gamma)
        p2i_gamma = p2is_assigned[i].evaluate(gamma)
        pk1i_gamma = pk1is_in_p[i].evaluate(gamma)
        ct1i_gamma = ct1is_in_p[i].evaluate(gamma)

        lhs = ct1i_gamma
        rhs = (pk1i_gamma * u_gamma + e1_gamma
               + p1i_gamma * qi_constants[i]
               + p2i_gamma * cyclo_gamma)
        assert lhs % p == rhs % p, f"Equation 2 failed for CRT basis {i}"

    print("All constraint checks passed!")

    # =========================================================================
    # ADVICE CELL COUNT ESTIMATION
    # =========================================================================

    phase_0_cells = 0
    phase_1_range_check_cells = 0
    phase_1_eval_at_gamma_cells = 0
    phase_1_constraint_poly_cells = 0

    # Phase 0: assign all polynomials
    for poly in [u_assigned, e0_assigned, e1_assigned, k1_assigned]:
        phase_0_cells += len(poly.coefficients)
    for i in range(len(ciphertexts)):
        for poly in [r1is_assigned[i], r2is_assigned[i], p1is_assigned[i], p2is_assigned[i]]:
            phase_0_cells += len(poly.coefficients)

    # Phase 1 range checks (shared polynomials)
    phase_1_range_check_cells += count_advice_cells_needed_for_poly_range_check(u_assigned, 2 * u_bound + 1, lookup_bits)
    phase_1_range_check_cells += count_advice_cells_needed_for_poly_range_check(e0_assigned, 2 * b + 1, lookup_bits)
    phase_1_range_check_cells += count_advice_cells_needed_for_poly_range_check(e1_assigned, 2 * b + 1, lookup_bits)
    phase_1_range_check_cells += count_advice_cells_needed_for_poly_range_check(k1_assigned, 2 * k1_bound + 1, lookup_bits)
    # Phase 1 range checks (per-CRT-basis polynomials)
    for i in range(len(ciphertexts)):
        phase_1_range_check_cells += count_advice_cells_needed_for_poly_range_check(r1is_assigned[i], 2 * r1_bounds[i] + 1, lookup_bits)
        phase_1_range_check_cells += count_advice_cells_needed_for_poly_range_check(r2is_assigned[i], 2 * r2_bounds[i] + 1, lookup_bits)
        phase_1_range_check_cells += count_advice_cells_needed_for_poly_range_check(p1is_assigned[i], 2 * p1_bounds[i] + 1, lookup_bits)
        phase_1_range_check_cells += count_advice_cells_needed_for_poly_range_check(p2is_assigned[i], 2 * p2_bounds[i] + 1, lookup_bits)

    # Phase 1 eval at gamma: 2*len-1 cells per polynomial
    for poly in [u_assigned, e0_assigned, e1_assigned, k1_assigned]:
        phase_1_eval_at_gamma_cells += 2 * len(poly.coefficients) - 1
    for i in range(len(ciphertexts)):
        for poly in [r1is_assigned[i], r2is_assigned[i], p1is_assigned[i], p2is_assigned[i]]:
            phase_1_eval_at_gamma_cells += 2 * len(poly.coefficients) - 1
    # cyclo polynomial: degree N (N+1 coefficients), shared across all CRT bases and equations
    phase_1_eval_at_gamma_cells += 2 * (n + 1) - 1

    # Phase 1 constraint: 16 cells per equation, 2 equations per CRT basis
    phase_1_constraint_poly_cells += len(ciphertexts) * 2 * 16

    total_cells = (phase_0_cells + phase_1_range_check_cells
                   + phase_1_eval_at_gamma_cells + phase_1_constraint_poly_cells)
    print_advice_cells_info(total_cells, phase_0_cells, phase_1_range_check_cells,
                            phase_1_eval_at_gamma_cells, phase_1_constraint_poly_cells)

    # =========================================================================
    # OUTPUT: JSON witness data
    # =========================================================================

    json_input = {
        "u": [str(coef) for coef in u_assigned.coefficients],
        "e0": [str(coef) for coef in e0_assigned.coefficients],
        "e1": [str(coef) for coef in e1_assigned.coefficients],
        "k1": [str(coef) for coef in k1_assigned.coefficients],
        "r1is": [[str(coef) for coef in r1i.coefficients] for r1i in r1is_assigned],
        "r2is": [[str(coef) for coef in r2i.coefficients] for r2i in r2is_assigned],
        "p1is": [[str(coef) for coef in p1i.coefficients] for p1i in p1is_assigned],
        "p2is": [[str(coef) for coef in p2i.coefficients] for p2i in p2is_assigned],
        "pk0is": [[str(coef) for coef in pk0i.coefficients] for pk0i in pk0is_in_p],
        "pk1is": [[str(coef) for coef in pk1i.coefficients] for pk1i in pk1is_in_p],
        "ct0is": [[str(coef) for coef in ct0i.coefficients] for ct0i in ct0is_in_p],
        "ct1is": [[str(coef) for coef in ct1i.coefficients] for ct1i in ct1is_in_p],
    }

    qis_bitsize = max(qis).bit_length()
    qis_len = len(qis)
    filename = f"pk_enc_{n}_{qis_len}x{qis_bitsize}_{t}.json"
    output_path = os.path.join("src", "data", filename)

    with open(output_path, 'w') as f:
        json.dump(json_input, f)
    print(f"Wrote witness data to {output_path}")

    # Zero witness for key generation
    json_input_zeroes = {
        "u": ["0" for _ in u_assigned.coefficients],
        "e0": ["0" for _ in e0_assigned.coefficients],
        "e1": ["0" for _ in e1_assigned.coefficients],
        "k1": ["0" for _ in k1_assigned.coefficients],
        "r1is": [["0" for _ in r1i.coefficients] for r1i in r1is_assigned],
        "r2is": [["0" for _ in r2i.coefficients] for r2i in r2is_assigned],
        "p1is": [["0" for _ in p1i.coefficients] for p1i in p1is_assigned],
        "p2is": [["0" for _ in p2i.coefficients] for p2i in p2is_assigned],
        "pk0is": [["0" for _ in pk0i.coefficients] for pk0i in pk0is_in_p],
        "pk1is": [["0" for _ in pk1i.coefficients] for pk1i in pk1is_in_p],
        "ct0is": [["0" for _ in ct0i.coefficients] for ct0i in ct0is_in_p],
        "ct1is": [["0" for _ in ct1i.coefficients] for ct1i in ct1is_in_p],
    }

    zeroes_filename = f"pk_enc_{n}_{qis_len}x{qis_bitsize}_{t}_zeroes.json"
    zeroes_output_path = os.path.join("src", "data", zeroes_filename)

    with open(zeroes_output_path, 'w') as f:
        json.dump(json_input_zeroes, f)
    print(f"Wrote zeroes data to {zeroes_output_path}")

    # =========================================================================
    # OUTPUT: Rust constants file
    # =========================================================================

    constants_filename = f"pk_enc_constants_{n}_{qis_len}x{qis_bitsize}_{t}.rs"
    constants_output_path = os.path.join("src", "constants", constants_filename)

    with open(constants_output_path, 'w') as f:
        f.write(f"/// `N` is the degree of the cyclotomic polynomial defining the ring `Rq = Zq[X]/(X^N + 1)`.\n")
        f.write(f"pub const N: usize = {n};\n")
        f.write(f"/// The coefficients of the polynomial `u` should exist in the interval `[-U_BOUND, U_BOUND]`.\n")
        f.write(f"pub const U_BOUND: u64 = {u_bound};\n")
        f.write(f"/// The coefficients of the polynomial `e0` should exist in the interval `[-E0_BOUND, E0_BOUND]`.\n")
        f.write(f"pub const E0_BOUND: u64 = {b};\n")
        f.write(f"/// The coefficients of the polynomial `e1` should exist in the interval `[-E1_BOUND, E1_BOUND]`.\n")
        f.write(f"pub const E1_BOUND: u64 = {b};\n")
        f.write(f"/// The coefficients of `k1` should exist in the interval `[-K1_BOUND, K1_BOUND]`.\n")
        f.write(f"pub const K1_BOUND: u64 = {k1_bound};\n")
        f.write(f"pub const R1_BOUNDS: [u64; {len(r1_bounds)}] = [{', '.join(map(str, r1_bounds))}];\n")
        f.write(f"pub const R2_BOUNDS: [u64; {len(r2_bounds)}] = [{', '.join(map(str, r2_bounds))}];\n")
        f.write(f"pub const P1_BOUNDS: [u64; {len(p1_bounds)}] = [{', '.join(map(str, p1_bounds))}];\n")
        f.write(f"pub const P2_BOUNDS: [u64; {len(p2_bounds)}] = [{', '.join(map(str, p2_bounds))}];\n")
        qis_str = ', '.join(f'"{q}"' for q in qi_constants)
        f.write(f"pub const QIS: [&str; {len(qi_constants)}] = [{qis_str}];\n")
        k0is_str = ', '.join(f'"{k0i}"' for k0i in k0i_constants)
        f.write(f"pub const K0IS: [&str; {len(k0i_constants)}] = [{k0is_str}];\n")

    print(f"Wrote Rust constants to {constants_output_path}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Generate rust constants and json inputs for BFV zk proof of PUBLIC KEY encryption circuit"
    )
    parser.add_argument(
        "-n", type=int, required=True, help="Degree of f(x), must be a power of 2."
    )
    parser.add_argument(
        "-qis", type=str, required=True, help="List of qis (JSON array of CRT moduli)."
    )
    parser.add_argument(
        "-t", type=int, required=True, help="Modulus t of the plaintext space."
    )
    args = parser.parse_args()
    main(args)
