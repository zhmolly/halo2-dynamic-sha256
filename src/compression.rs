use eth_types::Field;
use halo2_base::halo2_proofs::halo2curves::FieldExt;
use halo2_base::halo2_proofs::{
    circuit::{AssignedCell, Cell, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector, TableColumn,
        VirtualCells,
    },
    poly::Rotation,
};
use halo2_base::utils::fe_to_bigint;
use halo2_base::ContextParams;
use halo2_base::QuantumCell;
use halo2_base::{
    gates::{flex_gate::FlexGateConfig, range::RangeConfig, GateInstructions, RangeInstructions},
    utils::{bigint_to_fe, biguint_to_fe, fe_to_biguint, modulus, PrimeField},
    AssignedValue, Context,
};
use hex;
use itertools::Itertools;
use sha2::{Digest, Sha256};

const BLOCK_BYTE: usize = 64;
const DIGEST_BYTE: usize = 32;

pub fn sha256_compression<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    assigned_input_bytes: &[AssignedValue<'a, F>],
    pre_state_words: &[AssignedValue<'a, F>],
) -> Vec<AssignedValue<'a, F>> {
    debug_assert_eq!(assigned_input_bytes.len(), 64);
    debug_assert_eq!(pre_state_words.len(), 8);
    let gate = range.gate();
    // message schedule.
    let mut message_u32s = assigned_input_bytes
        .chunks(4)
        .map(|bytes| {
            let mut sum = gate.load_zero(ctx);
            for idx in 0..4 {
                sum = gate.mul_add(
                    ctx,
                    QuantumCell::Existing(&bytes[3 - idx]),
                    QuantumCell::Constant(F::from(1u64 << (8 * idx))),
                    QuantumCell::Existing(&sum),
                );
            }
            sum
        })
        .collect_vec();
    let mut message_bits = message_u32s
        .iter()
        .map(|val: &AssignedValue<F>| gate.num_to_bits(ctx, val, 32))
        .collect_vec();
    for idx in 16..64 {
        let term1_bits = sigma_s_generic(ctx, gate, &message_bits[idx - 2], 17, 19, 10);
        let term3_bits = sigma_s_generic(ctx, gate, &message_bits[idx - 15], 7, 18, 3);
        let term1_u32 = bits2u32(ctx, gate, &term1_bits);
        let term3_u32 = bits2u32(ctx, gate, &term3_bits);
        let new_w = {
            let add1 = gate.add(
                ctx,
                QuantumCell::Existing(&term1_u32),
                QuantumCell::Existing(&message_u32s[idx - 7]),
            );
            let add2 = gate.add(
                ctx,
                QuantumCell::Existing(&add1),
                QuantumCell::Existing(&term3_u32),
            );
            let add3 = gate.add(
                ctx,
                QuantumCell::Existing(&add2),
                QuantumCell::Existing(&message_u32s[idx - 16]),
            );
            mod_u32(ctx, &range, &add3)
        };
        message_u32s.push(new_w.clone());
        if idx <= 61 {
            let new_w_bits = gate.num_to_bits(ctx, &new_w, 32);
            message_bits.push(new_w_bits);
        }
    }

    // compression
    let (mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h) = (
        pre_state_words[0].clone(),
        pre_state_words[1].clone(),
        pre_state_words[2].clone(),
        pre_state_words[3].clone(),
        pre_state_words[4].clone(),
        pre_state_words[5].clone(),
        pre_state_words[6].clone(),
        pre_state_words[7].clone(),
    );
    let mut a_bits = gate.num_to_bits(ctx, &a, 32);
    let mut b_bits = gate.num_to_bits(ctx, &b, 32);
    let mut c_bits = gate.num_to_bits(ctx, &c, 32);
    let mut e_bits = gate.num_to_bits(ctx, &e, 32);
    let mut f_bits = gate.num_to_bits(ctx, &f, 32);
    let mut g_bits = gate.num_to_bits(ctx, &g, 32);
    let mut t1 = gate.load_zero(ctx);
    let mut t2 = gate.load_zero(ctx);
    for idx in 0..64 {
        t1 = {
            let sigma_term = sigma_l_generic(ctx, gate, &e_bits, 6, 11, 25);
            let sigma_term = bits2u32(ctx, gate, &sigma_term);
            let ch_term = ch(ctx, gate, &e_bits, &f_bits, &g_bits);
            let ch_term = bits2u32(ctx, gate, &ch_term);
            let add1 = gate.add(
                ctx,
                QuantumCell::Existing(&h),
                QuantumCell::Existing(&sigma_term),
            );
            let add2 = gate.add(
                ctx,
                QuantumCell::Existing(&add1),
                QuantumCell::Existing(&ch_term),
            );
            let k = gate.load_constant(ctx, F::from(ROUND_CONSTANTS[idx] as u64));
            let add3 = gate.add(
                ctx,
                QuantumCell::Existing(&add2),
                QuantumCell::Constant(F::from(ROUND_CONSTANTS[idx] as u64)),
            );
            let add4 = gate.add(
                ctx,
                QuantumCell::Existing(&add3),
                QuantumCell::Existing(&message_u32s[idx]),
            );
            mod_u32(ctx, &range, &add4)
        };
        t2 = {
            let sigma_term = sigma_l_generic(ctx, gate, &a_bits, 2, 13, 22);
            let sigma_term = bits2u32(ctx, gate, &sigma_term);
            let maj_term = maj(ctx, gate, &a_bits, &b_bits, &c_bits);
            let maj_term = bits2u32(ctx, gate, &maj_term);
            let add = gate.add(
                ctx,
                QuantumCell::Existing(&sigma_term),
                QuantumCell::Existing(&maj_term),
            );
            mod_u32(ctx, range, &add)
        };
        h = g;
        g = f;
        g_bits = f_bits;
        f = e;
        f_bits = e_bits;
        e = {
            let add = gate.add(ctx, QuantumCell::Existing(&d), QuantumCell::Existing(&t1));
            mod_u32(ctx, range, &add)
        };
        e_bits = gate.num_to_bits(ctx, &e, 32);
        d = c;
        c = b;
        c_bits = b_bits;
        b = a;
        b_bits = a_bits;
        a = {
            let add = gate.add(ctx, QuantumCell::Existing(&t1), QuantumCell::Existing(&t2));
            mod_u32(ctx, range, &add)
        };
        a_bits = gate.num_to_bits(ctx, &a, 32);
    }
    let new_states = vec![a, b, c, d, e, f, g, h];
    let next_state_words = new_states
        .iter()
        .zip(pre_state_words.iter())
        .map(|(x, y)| {
            let add = gate.add(ctx, QuantumCell::Existing(&x), QuantumCell::Existing(&y));
            mod_u32(ctx, range, &add)
        })
        .collect_vec();
    next_state_words
}

fn bits2u32<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    bits: &[AssignedValue<'a, F>],
) -> AssignedValue<'a, F> {
    debug_assert_eq!(bits.len(), 32);
    let mut sum = gate.load_zero(ctx);
    for idx in 0..32 {
        sum = gate.mul_add(
            ctx,
            QuantumCell::Existing(&bits[idx]),
            QuantumCell::Constant(F::from(1u64 << idx)),
            QuantumCell::Existing(&sum),
        );
    }
    sum
}

fn mod_u32<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    x: &AssignedValue<'a, F>,
) -> AssignedValue<'a, F> {
    let gate = range.gate();
    let lo = x
        .value()
        .map(|v| v.get_lower_32())
        .map(|v| F::from(v as u64));
    let hi = x
        .value()
        .map(|v| (v.get_lower_128() >> 32) & ((1u128 << 32) - 1))
        .map(|v| F::from(v as u64));
    let assigned_lo = gate.load_witness(ctx, lo);
    let assigned_hi = gate.load_witness(ctx, hi);
    range.range_check(ctx, &assigned_lo, 32);
    let composed = gate.mul_add(
        ctx,
        QuantumCell::Existing(&assigned_hi),
        QuantumCell::Constant(F::from(1u64 << 32)),
        QuantumCell::Existing(&assigned_lo),
    );
    gate.assert_equal(
        ctx,
        QuantumCell::Existing(&x),
        QuantumCell::Existing(&composed),
    );
    assigned_lo
}

fn ch<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    x_bits: &[AssignedValue<'a, F>],
    y_bits: &[AssignedValue<'a, F>],
    z_bits: &[AssignedValue<'a, F>],
) -> Vec<AssignedValue<'a, F>> {
    debug_assert_eq!(x_bits.len(), 32);
    debug_assert_eq!(y_bits.len(), 32);
    debug_assert_eq!(z_bits.len(), 32);

    // reference: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/ch.circom
    let y_sub_z = y_bits
        .iter()
        .zip(z_bits.iter())
        .map(|(y, z)| gate.sub(ctx, QuantumCell::Existing(&y), QuantumCell::Existing(&z)))
        .collect_vec();
    x_bits
        .iter()
        .zip(y_sub_z.iter())
        .zip(z_bits.iter())
        .map(|((x, y), z)| {
            gate.mul_add(
                ctx,
                QuantumCell::Existing(&x),
                QuantumCell::Existing(&y),
                QuantumCell::Existing(&z),
            )
        })
        .collect_vec()

    // let x_y = x_bits
    //     .iter()
    //     .zip(y_bits.iter())
    //     .map(|(x, y)| gate.and(ctx, QuantumCell::Existing(&x), QuantumCell::Existing(&y)))
    //     .collect_vec();
    // let not_x_z = x_bits
    //     .iter()
    //     .zip(z_bits.iter())
    //     .map(|(x, z)| {
    //         let not_x = gate.not(ctx, QuantumCell::Existing(&x));
    //         gate.and(
    //             ctx,
    //             QuantumCell::Existing(&not_x),
    //             QuantumCell::Existing(&z),
    //         )
    //     })
    //     .collect_vec();
    // x_y.iter()
    //     .zip(not_x_z.iter())
    //     .map(|(a, b)| xor(ctx, gate, a, b))
    //     .collect_vec()
}

fn maj<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    x_bits: &[AssignedValue<'a, F>],
    y_bits: &[AssignedValue<'a, F>],
    z_bits: &[AssignedValue<'a, F>],
) -> Vec<AssignedValue<'a, F>> {
    debug_assert_eq!(x_bits.len(), 32);
    debug_assert_eq!(y_bits.len(), 32);
    debug_assert_eq!(z_bits.len(), 32);
    // reference: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/maj.circom
    let mid = y_bits
        .iter()
        .zip(z_bits.iter())
        .map(|(y, z)| gate.mul(ctx, QuantumCell::Existing(&y), QuantumCell::Existing(&z)))
        .collect_vec();
    (0..32)
        .map(|idx| {
            let add1 = gate.add(
                ctx,
                QuantumCell::Existing(&y_bits[idx]),
                QuantumCell::Existing(&z_bits[idx]),
            );
            let add2 = gate.mul_add(
                ctx,
                QuantumCell::Existing(&mid[idx]),
                QuantumCell::Constant(-F::from(2u64)),
                QuantumCell::Existing(&add1),
            );
            gate.mul_add(
                ctx,
                QuantumCell::Existing(&x_bits[idx]),
                QuantumCell::Existing(&add2),
                QuantumCell::Existing(&mid[idx]),
            )
        })
        .collect_vec()
    // let x_y = x_bits
    //     .iter()
    //     .zip(y_bits.iter())
    //     .map(|(x, y)| gate.and(ctx, QuantumCell::Existing(&x), QuantumCell::Existing(&y)))
    //     .collect_vec();
    // let x_z = x_bits
    //     .iter()
    //     .zip(z_bits.iter())
    //     .map(|(x, z)| gate.and(ctx, QuantumCell::Existing(&x), QuantumCell::Existing(&z)))
    //     .collect_vec();
    // let y_z = y_bits
    //     .iter()
    //     .zip(z_bits.iter())
    //     .map(|(y, z)| gate.and(ctx, QuantumCell::Existing(&y), QuantumCell::Existing(&z)))
    //     .collect_vec();
    // let xor1 = x_y
    //     .iter()
    //     .zip(x_z.iter())
    //     .map(|(a, b)| xor(ctx, gate, a, b))
    //     .collect_vec();
    // xor1.iter()
    //     .zip(y_z.iter())
    //     .map(|(a, b)| xor(ctx, gate, a, b))
    //     .collect_vec()
}

fn sigma_l_generic<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    x_bits: &[AssignedValue<'a, F>],
    n1: usize,
    n2: usize,
    n3: usize,
) -> Vec<AssignedValue<'a, F>> {
    let rotr1 = rotr(ctx, gate, x_bits, n1);
    let rotr2 = rotr(ctx, gate, x_bits, n2);
    let rotr3 = rotr(ctx, gate, x_bits, n3);
    rotr1
        .iter()
        .zip(rotr2.iter())
        .zip(rotr3.iter())
        .map(|((a, b), c)| xor3(ctx, gate, a, b, c))
        .collect_vec()
}

fn sigma_s_generic<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    x_bits: &[AssignedValue<'a, F>],
    n1: usize,
    n2: usize,
    n3: usize,
) -> Vec<AssignedValue<'a, F>> {
    let rotr1 = rotr(ctx, gate, x_bits, n1);
    let rotr2 = rotr(ctx, gate, x_bits, n2);
    let shr = shr(ctx, gate, x_bits, n3);
    rotr1
        .iter()
        .zip(rotr2.iter())
        .zip(shr.iter())
        .map(|((a, b), c)| xor3(ctx, gate, a, b, c))
        .collect_vec()
}

fn rotr<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    x_bits: &[AssignedValue<'a, F>],
    n: usize,
) -> Vec<AssignedValue<'a, F>> {
    debug_assert_eq!(x_bits.len(), 32);
    // reference: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/rotate.circom
    (0..32)
        .map(|idx| x_bits[(idx + n) % 32].clone())
        .collect_vec()
}

fn shr<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    x_bits: &[AssignedValue<'a, F>],
    n: usize,
) -> Vec<AssignedValue<'a, F>> {
    debug_assert_eq!(x_bits.len(), 32);
    // referece: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/shift.circom
    let zero = gate.load_zero(ctx);
    (0..32)
        .map(|idx| {
            if idx + n >= 32 {
                zero.clone()
            } else {
                x_bits[idx + n].clone()
            }
        })
        .collect_vec()
}

fn left_shift<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    x_bits: &[AssignedValue<'a, F>],
    n: usize,
) -> Vec<AssignedValue<'a, F>> {
    debug_assert_eq!(x_bits.len(), 32);
    let zero = gate.load_zero(ctx);
    let padding = (0..n).map(|_| zero.clone()).collect_vec();
    vec![&x_bits[n..32], &padding].concat()
}

fn xor3<'a, 'b: 'a, F: FieldExt>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    a: &AssignedValue<'a, F>,
    b: &AssignedValue<'a, F>,
    c: &AssignedValue<'a, F>,
) -> AssignedValue<'a, F> {
    // referece: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/xor3.circom
    let mid = gate.mul(ctx, QuantumCell::Existing(&b), QuantumCell::Existing(&c));
    let mid_term = gate.mul_add(
        ctx,
        QuantumCell::Existing(&b),
        QuantumCell::Constant(-F::from(2u64)),
        QuantumCell::Constant(F::from(1u64)),
    );
    let mid_term = gate.mul_add(
        ctx,
        QuantumCell::Existing(&c),
        QuantumCell::Constant(-F::from(2u64)),
        QuantumCell::Existing(&mid_term),
    );
    let mid_term = gate.mul_add(
        ctx,
        QuantumCell::Existing(&mid),
        QuantumCell::Constant(F::from(4u64)),
        QuantumCell::Existing(&mid_term),
    );
    let b_c = gate.add(ctx, QuantumCell::Existing(&b), QuantumCell::Existing(&c));
    let add_term = gate.mul_add(
        ctx,
        QuantumCell::Existing(&mid),
        QuantumCell::Constant(-F::from(2u64)),
        QuantumCell::Existing(&b_c),
    );
    gate.mul_add(
        ctx,
        QuantumCell::Existing(&a),
        QuantumCell::Existing(&mid_term),
        QuantumCell::Existing(&add_term),
    )
}

pub const NUM_ROUND: usize = 64;
pub const NUM_STATE_WORD: usize = 8;
const ROUND_CONSTANTS: [u32; NUM_ROUND] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

pub const INIT_STATE: [u32; NUM_STATE_WORD] = [
    0x6a09_e667,
    0xbb67_ae85,
    0x3c6e_f372,
    0xa54f_f53a,
    0x510e_527f,
    0x9b05_688c,
    0x1f83_d9ab,
    0x5be0_cd19,
];
