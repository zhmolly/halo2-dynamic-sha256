use crate::spread::SpreadConfig;
use crate::utils::{bits_le_to_fe, fe_to_bits_le};
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

// const BLOCK_BYTE: usize = 64;
// const DIGEST_BYTE: usize = 32;

pub type SpreadU32<'a, F> = (AssignedValue<'a, F>, AssignedValue<'a, F>);

pub fn sha256_compression<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    assigned_input_bytes: &[AssignedValue<'a, F>],
    pre_state_words: &[AssignedValue<'a, F>],
) -> Result<Vec<AssignedValue<'a, F>>, Error> {
    debug_assert_eq!(assigned_input_bytes.len(), 64);
    debug_assert_eq!(pre_state_words.len(), 8);
    let gate = range.gate();
    // message schedule.
    let mut i = 0;
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
            i += 1;
            // println!("idx {} sum {:?}", i, sum.value());
            sum
        })
        .collect_vec();

    // let mut message_bits = message_u32s
    //     .iter()
    //     .map(|val: &AssignedValue<F>| gate.num_to_bits(ctx, val, 32))
    //     .collect_vec();
    let mut message_spreads = message_u32s
        .iter()
        .map(|dense| state_to_spread_u32(ctx, range, spread_config, dense))
        .collect::<Result<Vec<SpreadU32<F>>, Error>>()?;
    for idx in 16..64 {
        // let w_2_spread = state_to_spread_u32(ctx, range, spread_config, &message_u32s[idx - 2])?;
        // let w_15_spread = state_to_spread_u32(ctx, range, spread_config, &message_u32s[idx - 15])?;
        let term1 = sigma_lower1(ctx, range, spread_config, &message_spreads[idx - 2])?;
        let term3 = sigma_lower0(ctx, range, spread_config, &message_spreads[idx - 15])?;
        // let term1_u32 = bits2u32(ctx, gate, &term1_bits);
        // let term3_u32 = bits2u32(ctx, gate, &term3_bits);
        let new_w = {
            let mut sum = gate.add(
                ctx,
                QuantumCell::Existing(&term1),
                QuantumCell::Existing(&message_u32s[idx - 7]),
            );
            sum = gate.add(
                ctx,
                QuantumCell::Existing(&sum),
                QuantumCell::Existing(&term3),
            );
            sum = gate.add(
                ctx,
                QuantumCell::Existing(&sum),
                QuantumCell::Existing(&message_u32s[idx - 16]),
            );
            mod_u32(ctx, &range, &sum)
        };
        // println!(
        //     "idx {} term1 {:?}, term3 {:?}, new_w {:?}",
        //     idx,
        //     term1.value(),
        //     term3.value(),
        //     new_w.value()
        // );
        message_u32s.push(new_w.clone());
        let new_w_spread = state_to_spread_u32(ctx, range, spread_config, &new_w)?;
        message_spreads.push(new_w_spread);
        // if idx <= 61 {
        //     let new_w_bits = gate.num_to_bits(ctx, &new_w, 32);
        //     message_bits.push(new_w_bits);
        // }
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
    let mut a_spread = state_to_spread_u32(ctx, range, spread_config, &a)?;
    let mut b_spread = state_to_spread_u32(ctx, range, spread_config, &b)?;
    let mut c_spread = state_to_spread_u32(ctx, range, spread_config, &c)?;
    // let mut d_spread = state_to_spread_u32(ctx, range, spread_config, &d)?;
    let mut e_spread = state_to_spread_u32(ctx, range, spread_config, &e)?;
    let mut f_spread = state_to_spread_u32(ctx, range, spread_config, &f)?;
    let mut g_spread = state_to_spread_u32(ctx, range, spread_config, &g)?;
    // let mut h_spread = state_to_spread_u32(ctx, range, spread_config, &h)?;
    // let mut a_bits = gate.num_to_bits(ctx, &a, 32);
    // let mut b_bits = gate.num_to_bits(ctx, &b, 32);
    // let mut c_bits = gate.num_to_bits(ctx, &c, 32);
    // let mut e_bits = gate.num_to_bits(ctx, &e, 32);
    // let mut f_bits = gate.num_to_bits(ctx, &f, 32);
    // let mut g_bits = gate.num_to_bits(ctx, &g, 32);
    let mut t1 = gate.load_zero(ctx);
    let mut t2 = gate.load_zero(ctx);
    for idx in 0..64 {
        t1 = {
            // let e_spread = state_to_spread_u32(ctx, range, spread_config, &e)?;
            // let f_spread = state_to_spread_u32(ctx, range, spread_config, &f)?;
            // let g_spread = state_to_spread_u32(ctx, range, spread_config, &g)?;
            let sigma_term = sigma_upper1(ctx, range, spread_config, &e_spread)?;
            let ch_term = ch(ctx, range, spread_config, &e_spread, &f_spread, &g_spread)?;
            // println!(
            //     "idx {} sigma {:?} ch {:?}",
            //     idx,
            //     sigma_term.value(),
            //     ch_term.value()
            // );
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
            // let a_spread = state_to_spread_u32(ctx, range, spread_config, &a)?;
            // let b_spread = state_to_spread_u32(ctx, range, spread_config, &b)?;
            // let c_spread = state_to_spread_u32(ctx, range, spread_config, &c)?;
            let sigma_term = sigma_upper0(ctx, range, spread_config, &a_spread)?;
            let maj_term = maj(ctx, range, spread_config, &a_spread, &b_spread, &c_spread)?;
            let add = gate.add(
                ctx,
                QuantumCell::Existing(&sigma_term),
                QuantumCell::Existing(&maj_term),
            );
            mod_u32(ctx, range, &add)
        };
        // println!("idx {}, t1 {:?}, t2 {:?}", idx, t1.value(), t2.value());
        h = g;
        // h_spread = g_spread;
        g = f;
        g_spread = f_spread;
        f = e;
        f_spread = e_spread;
        e = {
            let add = gate.add(ctx, QuantumCell::Existing(&d), QuantumCell::Existing(&t1));
            mod_u32(ctx, range, &add)
        };
        e_spread = state_to_spread_u32(ctx, range, spread_config, &e)?;
        d = c;
        // d_spread = c_spread;
        c = b;
        c_spread = b_spread;
        b = a;
        b_spread = a_spread;
        a = {
            let add = gate.add(ctx, QuantumCell::Existing(&t1), QuantumCell::Existing(&t2));
            mod_u32(ctx, range, &add)
        };
        a_spread = state_to_spread_u32(ctx, range, spread_config, &a)?;
    }
    let new_states = vec![a, b, c, d, e, f, g, h];
    let next_state_words = new_states
        .iter()
        .zip(pre_state_words.iter())
        .map(|(x, y)| {
            let add = gate.add(ctx, QuantumCell::Existing(&x), QuantumCell::Existing(&y));
            // println!(
            //     "pre {:?} new {:?} add {:?}",
            //     y.value(),
            //     x.value(),
            //     add.value()
            // );
            mod_u32(ctx, range, &add)
        })
        .collect_vec();
    Ok(next_state_words)
}

fn state_to_spread_u32<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    x: &AssignedValue<F>,
) -> Result<SpreadU32<'a, F>, Error> {
    let gate = range.gate();
    let lo = x
        .value()
        .map(|v| v.get_lower_32() & ((1 << 16) - 1))
        .map(|v| F::from(v as u64));
    let hi = x
        .value()
        .map(|v| (v.get_lower_32() >> 16))
        .map(|v| F::from(v as u64));
    let assigned_lo = gate.load_witness(ctx, lo);
    let assigned_hi = gate.load_witness(ctx, hi);
    let composed = gate.mul_add(
        ctx,
        QuantumCell::Existing(&assigned_hi),
        QuantumCell::Constant(F::from(1u64 << 16)),
        QuantumCell::Existing(&assigned_lo),
    );
    gate.assert_equal(
        ctx,
        QuantumCell::Existing(&x),
        QuantumCell::Existing(&composed),
    );
    let lo_spread = spread_config.spread(ctx, range, &assigned_lo)?;
    let hi_spread = spread_config.spread(ctx, range, &assigned_hi)?;
    Ok((lo_spread, hi_spread))
}

// fn bits2u32<'a, 'b: 'a, F: FieldExt>(
//     ctx: &mut Context<'b, F>,
//     gate: &FlexGateConfig<F>,
//     bits: &[AssignedValue<'a, F>],
// ) -> AssignedValue<'a, F> {
//     debug_assert_eq!(bits.len(), 32);
//     let mut sum = gate.load_zero(ctx);
//     for idx in 0..32 {
//         sum = gate.mul_add(
//             ctx,
//             QuantumCell::Existing(&bits[idx]),
//             QuantumCell::Constant(F::from(1u64 << idx)),
//             QuantumCell::Existing(&sum),
//         );
//     }
//     sum
// }

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

fn ch<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    x: &SpreadU32<'a, F>,
    y: &SpreadU32<'a, F>,
    z: &SpreadU32<'a, F>,
) -> Result<AssignedValue<'a, F>, Error> {
    let (x_lo, x_hi) = x;
    let (y_lo, y_hi) = y;
    let (z_lo, z_hi) = z;
    let gate = range.gate();
    let p_lo = gate.add(
        ctx,
        QuantumCell::Existing(&x_lo),
        QuantumCell::Existing(&y_lo),
    );
    let p_hi = gate.add(
        ctx,
        QuantumCell::Existing(&x_hi),
        QuantumCell::Existing(&y_hi),
    );
    const MASK_EVEN_32: u64 = 0x55555555;
    let x_neg_lo = gate.neg(ctx, QuantumCell::Existing(&x_lo));
    let x_neg_hi = gate.neg(ctx, QuantumCell::Existing(&x_hi));
    let q_lo = three_add(
        ctx,
        gate,
        QuantumCell::Constant(F::from(MASK_EVEN_32)),
        QuantumCell::Existing(&x_neg_lo),
        QuantumCell::Existing(&z_lo),
    );
    let q_hi = three_add(
        ctx,
        gate,
        QuantumCell::Constant(F::from(MASK_EVEN_32)),
        QuantumCell::Existing(&x_neg_hi),
        QuantumCell::Existing(&z_hi),
    );
    let (p_lo_even, p_lo_odd) =
        spread_config.decompose_even_and_odd_unchecked(ctx, range, &p_lo)?;
    let (p_hi_even, p_hi_odd) =
        spread_config.decompose_even_and_odd_unchecked(ctx, range, &p_hi)?;
    let (q_lo_even, q_lo_odd) =
        spread_config.decompose_even_and_odd_unchecked(ctx, range, &q_lo)?;
    let (q_hi_even, q_hi_odd) =
        spread_config.decompose_even_and_odd_unchecked(ctx, range, &q_hi)?;
    {
        let even_spread = spread_config.spread(ctx, range, &p_lo_even)?;
        let odd_spread = spread_config.spread(ctx, range, &p_lo_odd)?;
        let sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(2)),
            QuantumCell::Existing(&odd_spread),
            QuantumCell::Existing(&even_spread),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&sum),
            QuantumCell::Existing(&p_lo),
        );
    }
    {
        let even_spread = spread_config.spread(ctx, range, &p_hi_even)?;
        let odd_spread = spread_config.spread(ctx, range, &p_hi_odd)?;
        let sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(2)),
            QuantumCell::Existing(&odd_spread),
            QuantumCell::Existing(&even_spread),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&sum),
            QuantumCell::Existing(&p_hi),
        );
    }
    {
        let even_spread = spread_config.spread(ctx, range, &q_lo_even)?;
        let odd_spread = spread_config.spread(ctx, range, &q_lo_odd)?;
        let sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(2)),
            QuantumCell::Existing(&odd_spread),
            QuantumCell::Existing(&even_spread),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&sum),
            QuantumCell::Existing(&q_lo),
        );
    }
    {
        let even_spread = spread_config.spread(ctx, range, &q_hi_even)?;
        let odd_spread = spread_config.spread(ctx, range, &q_hi_odd)?;
        let sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(2)),
            QuantumCell::Existing(&odd_spread),
            QuantumCell::Existing(&even_spread),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&sum),
            QuantumCell::Existing(&q_hi),
        );
    }
    let out_lo = gate.add(
        ctx,
        QuantumCell::Existing(&p_lo_odd),
        QuantumCell::Existing(&q_lo_odd),
    );
    let out_hi = gate.add(
        ctx,
        QuantumCell::Existing(&p_hi_odd),
        QuantumCell::Existing(&q_hi_odd),
    );
    let out = gate.mul_add(
        ctx,
        QuantumCell::Existing(&out_hi),
        QuantumCell::Constant(F::from(1u64 << 16)),
        QuantumCell::Existing(&out_lo),
    );
    Ok(out)
}

// fn ch<'a, 'b: 'a, F: FieldExt>(
//     ctx: &mut Context<'b, F>,
//     gate: &FlexGateConfig<F>,
//     x_bits: &[AssignedValue<'a, F>],
//     y_bits: &[AssignedValue<'a, F>],
//     z_bits: &[AssignedValue<'a, F>],
// ) -> Vec<AssignedValue<'a, F>> {
//     debug_assert_eq!(x_bits.len(), 32);
//     debug_assert_eq!(y_bits.len(), 32);
//     debug_assert_eq!(z_bits.len(), 32);

//     // reference: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/ch.circom
//     let y_sub_z = y_bits
//         .iter()
//         .zip(z_bits.iter())
//         .map(|(y, z)| gate.sub(ctx, QuantumCell::Existing(&y), QuantumCell::Existing(&z)))
//         .collect_vec();
//     x_bits
//         .iter()
//         .zip(y_sub_z.iter())
//         .zip(z_bits.iter())
//         .map(|((x, y), z)| {
//             gate.mul_add(
//                 ctx,
//                 QuantumCell::Existing(&x),
//                 QuantumCell::Existing(&y),
//                 QuantumCell::Existing(&z),
//             )
//         })
//         .collect_vec()

//     // let x_y = x_bits
//     //     .iter()
//     //     .zip(y_bits.iter())
//     //     .map(|(x, y)| gate.and(ctx, QuantumCell::Existing(&x), QuantumCell::Existing(&y)))
//     //     .collect_vec();
//     // let not_x_z = x_bits
//     //     .iter()
//     //     .zip(z_bits.iter())
//     //     .map(|(x, z)| {
//     //         let not_x = gate.not(ctx, QuantumCell::Existing(&x));
//     //         gate.and(
//     //             ctx,
//     //             QuantumCell::Existing(&not_x),
//     //             QuantumCell::Existing(&z),
//     //         )
//     //     })
//     //     .collect_vec();
//     // x_y.iter()
//     //     .zip(not_x_z.iter())
//     //     .map(|(a, b)| xor(ctx, gate, a, b))
//     //     .collect_vec()

fn maj<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    x: &SpreadU32<'a, F>,
    y: &SpreadU32<'a, F>,
    z: &SpreadU32<'a, F>,
) -> Result<AssignedValue<'a, F>, Error> {
    let (x_lo, x_hi) = x;
    let (y_lo, y_hi) = y;
    let (z_lo, z_hi) = z;
    let gate = range.gate();
    let m_lo = three_add(
        ctx,
        range.gate(),
        QuantumCell::Existing(&x_lo),
        QuantumCell::Existing(&y_lo),
        QuantumCell::Existing(&z_lo),
    );
    let m_hi = three_add(
        ctx,
        range.gate(),
        QuantumCell::Existing(&x_hi),
        QuantumCell::Existing(&y_hi),
        QuantumCell::Existing(&z_hi),
    );
    let (m_lo_even, m_lo_odd) =
        spread_config.decompose_even_and_odd_unchecked(ctx, range, &m_lo)?;
    let (m_hi_even, m_hi_odd) =
        spread_config.decompose_even_and_odd_unchecked(ctx, range, &m_hi)?;
    {
        let even_spread = spread_config.spread(ctx, range, &m_lo_even)?;
        let odd_spread = spread_config.spread(ctx, range, &m_lo_odd)?;
        let sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(2)),
            QuantumCell::Existing(&odd_spread),
            QuantumCell::Existing(&even_spread),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&sum),
            QuantumCell::Existing(&m_lo),
        );
    }
    {
        let even_spread = spread_config.spread(ctx, range, &m_hi_even)?;
        let odd_spread = spread_config.spread(ctx, range, &m_hi_odd)?;
        let sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(2)),
            QuantumCell::Existing(&odd_spread),
            QuantumCell::Existing(&even_spread),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&sum),
            QuantumCell::Existing(&m_hi),
        );
    }
    let m = gate.mul_add(
        ctx,
        QuantumCell::Existing(&m_hi_odd),
        QuantumCell::Constant(F::from(1u64 << 16)),
        QuantumCell::Existing(&m_lo_odd),
    );
    Ok(m)
}

fn three_add<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    gate: &FlexGateConfig<F>,
    x: QuantumCell<'a, 'a, F>,
    y: QuantumCell<'a, 'a, F>,
    z: QuantumCell<'a, 'a, F>,
) -> AssignedValue<'a, F> {
    let add1 = gate.add(ctx, x, y);
    gate.add(ctx, QuantumCell::Existing(&add1), z)
}

// fn maj<'a, 'b: 'a, F: FieldExt>(
//     ctx: &mut Context<'b, F>,
//     gate: &FlexGateConfig<F>,
//     x_bits: &[AssignedValue<'a, F>],
//     y_bits: &[AssignedValue<'a, F>],
//     z_bits: &[AssignedValue<'a, F>],
// ) -> Vec<AssignedValue<'a, F>> {
//     debug_assert_eq!(x_bits.len(), 32);
//     debug_assert_eq!(y_bits.len(), 32);
//     debug_assert_eq!(z_bits.len(), 32);
//     // reference: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/maj.circom
//     let mid = y_bits
//         .iter()
//         .zip(z_bits.iter())
//         .map(|(y, z)| gate.mul(ctx, QuantumCell::Existing(&y), QuantumCell::Existing(&z)))
//         .collect_vec();
//     (0..32)
//         .map(|idx| {
//             let add1 = gate.add(
//                 ctx,
//                 QuantumCell::Existing(&y_bits[idx]),
//                 QuantumCell::Existing(&z_bits[idx]),
//             );
//             let add2 = gate.mul_add(
//                 ctx,
//                 QuantumCell::Existing(&mid[idx]),
//                 QuantumCell::Constant(-F::from(2u64)),
//                 QuantumCell::Existing(&add1),
//             );
//             gate.mul_add(
//                 ctx,
//                 QuantumCell::Existing(&x_bits[idx]),
//                 QuantumCell::Existing(&add2),
//                 QuantumCell::Existing(&mid[idx]),
//             )
//         })
//         .collect_vec()
//     // let x_y = x_bits
//     //     .iter()
//     //     .zip(y_bits.iter())
//     //     .map(|(x, y)| gate.and(ctx, QuantumCell::Existing(&x), QuantumCell::Existing(&y)))
//     //     .collect_vec();
//     // let x_z = x_bits
//     //     .iter()
//     //     .zip(z_bits.iter())
//     //     .map(|(x, z)| gate.and(ctx, QuantumCell::Existing(&x), QuantumCell::Existing(&z)))
//     //     .collect_vec();
//     // let y_z = y_bits
//     //     .iter()
//     //     .zip(z_bits.iter())
//     //     .map(|(y, z)| gate.and(ctx, QuantumCell::Existing(&y), QuantumCell::Existing(&z)))
//     //     .collect_vec();
//     // let xor1 = x_y
//     //     .iter()
//     //     .zip(x_z.iter())
//     //     .map(|(a, b)| xor(ctx, gate, a, b))
//     //     .collect_vec();
//     // xor1.iter()
//     //     .zip(y_z.iter())
//     //     .map(|(a, b)| xor(ctx, gate, a, b))
//     //     .collect_vec()
// }
fn sigma_upper0<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    x_spread: &SpreadU32<F>,
) -> Result<AssignedValue<'a, F>, Error> {
    const STARTS: [usize; 4] = [0, 2, 13, 22];
    const ENDS: [usize; 4] = [2, 13, 22, 32];
    const PADDINGS: [usize; 4] = [6, 5, 7, 6];
    let coeffs = [
        F::from((1u64 << 60) + (1u64 << 38) + (1u64 << 20)),
        F::from((1u64 << 0) + (1u64 << 42) + (1u64 << 24)),
        F::from((1u64 << 22) + (1u64 << 0) + (1u64 << 46)),
        F::from((1u64 << 40) + (1u64 << 18) + (1u64 << 0)),
    ];
    sigma_generic(
        ctx,
        range,
        spread_config,
        x_spread,
        &STARTS,
        &ENDS,
        &PADDINGS,
        &coeffs,
    )
}

fn sigma_upper1<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    x_spread: &SpreadU32<F>,
) -> Result<AssignedValue<'a, F>, Error> {
    const STARTS: [usize; 4] = [0, 6, 11, 25];
    const ENDS: [usize; 4] = [6, 11, 25, 32];
    const PADDINGS: [usize; 4] = [2, 3, 2, 1];
    let coeffs = [
        F::from((1u64 << 52) + (1u64 << 42) + (1u64 << 14)),
        F::from((1u64 << 0) + (1u64 << 54) + (1u64 << 26)),
        F::from((1u64 << 10) + (1u64 << 0) + (1u64 << 36)),
        F::from((1u64 << 38) + (1u64 << 28) + (1u64 << 0)),
    ];
    sigma_generic(
        ctx,
        range,
        spread_config,
        x_spread,
        &STARTS,
        &ENDS,
        &PADDINGS,
        &coeffs,
    )
}

fn sigma_lower0<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    x_spread: &SpreadU32<F>,
) -> Result<AssignedValue<'a, F>, Error> {
    const STARTS: [usize; 4] = [0, 3, 7, 18];
    const ENDS: [usize; 4] = [3, 7, 18, 32];
    const PADDINGS: [usize; 4] = [5, 4, 5, 2];
    let coeffs = [
        F::from((1u64 << 50) + (1u64 << 28)),
        F::from((1u64 << 0) + (1u64 << 56) + (1u64 << 34)),
        F::from((1u64 << 8) + (1u64 << 0) + (1u64 << 42)),
        F::from((1u64 << 30) + (1u64 << 22) + (1u64 << 0)),
    ];
    sigma_generic(
        ctx,
        range,
        spread_config,
        x_spread,
        &STARTS,
        &ENDS,
        &PADDINGS,
        &coeffs,
    )
}

fn sigma_lower1<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    x_spread: &SpreadU32<F>,
) -> Result<AssignedValue<'a, F>, Error> {
    const STARTS: [usize; 4] = [0, 10, 17, 19];
    const ENDS: [usize; 4] = [10, 17, 19, 32];
    const PADDINGS: [usize; 4] = [6, 1, 6, 3];
    let coeffs = [
        F::from((1u64 << 30) + (1u64 << 26)),
        F::from((1u64 << 0) + (1u64 << 50) + (1u64 << 46)),
        F::from((1u64 << 14) + (1u64 << 0) + (1u64 << 60)),
        F::from((1u64 << 18) + (1u64 << 4) + (1u64 << 0)),
    ];
    sigma_generic(
        ctx,
        range,
        spread_config,
        x_spread,
        &STARTS,
        &ENDS,
        &PADDINGS,
        &coeffs,
    )
}

fn sigma_generic<'a, 'b: 'a, F: PrimeField>(
    ctx: &mut Context<'b, F>,
    range: &RangeConfig<F>,
    spread_config: &mut SpreadConfig<F>,
    x_spread: &SpreadU32<F>,
    starts: &[usize; 4],
    ends: &[usize; 4],
    paddings: &[usize; 4],
    coeffs: &[F; 4],
) -> Result<AssignedValue<'a, F>, Error> {
    let gate = range.gate();
    // let x_spread = spread_config.spread(ctx, range, x)?;
    let bits_val = x_spread.0.value().zip(x_spread.1.value()).map(|(lo, hi)| {
        let mut bits = fe_to_bits_le(lo, 32);
        bits.append(&mut fe_to_bits_le(hi, 32));
        bits
    });
    let mut assign_bits =
        |bits_val: &Value<Vec<bool>>, start: usize, end: usize, padding: usize| {
            let fe_val: Value<F> = bits_val.as_ref().map(|bits| {
                let mut bits = bits[(2 * start)..(2 * end)].to_vec();
                bits.extend_from_slice(&vec![false; 64 - bits.len()]);
                bits_le_to_fe(&bits)
            });
            let assigned = gate.load_witness(ctx, fe_val);
            // let assigned_spread = spread_config.spread(ctx, range, &assigned_dense)?;
            // let result: Result<AssignedValue<F>, Error> = Ok(assigned_spread);
            assigned
        };
    let assigned_a = assign_bits(&bits_val, starts[0], ends[0], paddings[0]);
    let assigned_b = assign_bits(&bits_val, starts[1], ends[1], paddings[1]);
    let assigned_c = assign_bits(&bits_val, starts[2], ends[2], paddings[2]);
    let assigned_d = assign_bits(&bits_val, starts[3], ends[3], paddings[3]);
    {
        let mut sum = assigned_a.clone();
        sum = gate.mul_add(
            ctx,
            QuantumCell::Existing(&assigned_b),
            QuantumCell::Constant(F::from(1 << (2 * starts[1]))),
            QuantumCell::Existing(&sum),
        );
        sum = gate.mul_add(
            ctx,
            QuantumCell::Existing(&assigned_c),
            QuantumCell::Constant(F::from(1 << (2 * starts[2]))),
            QuantumCell::Existing(&sum),
        );
        sum = gate.mul_add(
            ctx,
            QuantumCell::Existing(&assigned_d),
            QuantumCell::Constant(F::from(1 << (2 * starts[3]))),
            QuantumCell::Existing(&sum),
        );
        let x_composed = gate.mul_add(
            ctx,
            QuantumCell::Existing(&x_spread.1),
            QuantumCell::Constant(F::from(1 << 32)),
            QuantumCell::Existing(&x_spread.0),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&x_composed),
            QuantumCell::Existing(&sum),
        );
    };
    // println!(
    //     "x {:?}, a {:?}, b {:?}, c {:?}, d {:?}",
    //     x.value(),
    //     assigned_a,
    //     assigned_b,
    //     assigned_c,
    //     assigned_d
    // );
    let r_spread = {
        // let a_coeff = F::from(1u64 << 60 + 1u64 << 38 + 1u64 << 20);
        // let b_coeff = F::from(1u64 << 0 + 1u64 << 42 + 1u64 << 24);
        // let c_coeff = F::from(1u64 << 22 + 1u64 << 0 + 1u64 << 46);
        // let d_coeff = F::from(1u64 << 40 + 1u64 << 18 + 1u64 << 0);
        let mut sum = gate.load_zero(ctx);
        // let assigned_a_spread = spread_config.spread(ctx, range, &assigned_a)?;
        // let assigned_b_spread = spread_config.spread(ctx, range, &assigned_b)?;
        // let assigned_c_spread = spread_config.spread(ctx, range, &assigned_c)?;
        // let assigned_d_spread = spread_config.spread(ctx, range, &assigned_d)?;
        sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(coeffs[0]),
            QuantumCell::Existing(&assigned_a),
            QuantumCell::Existing(&sum),
        );
        sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(coeffs[1]),
            QuantumCell::Existing(&assigned_b),
            QuantumCell::Existing(&sum),
        );
        sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(coeffs[2]),
            QuantumCell::Existing(&assigned_c),
            QuantumCell::Existing(&sum),
        );
        sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(coeffs[3]),
            QuantumCell::Existing(&assigned_d),
            QuantumCell::Existing(&sum),
        );
        sum
    };
    let (r_lo, r_hi) = {
        let lo = r_spread
            .value()
            .map(|v| v.get_lower_32())
            .map(|v| F::from(v as u64));
        let hi = r_spread
            .value()
            .map(|v| (v.get_lower_128() >> 32) & ((1u128 << 32) - 1))
            .map(|v| F::from(v as u64));
        let assigned_lo = gate.load_witness(ctx, lo);
        let assigned_hi = gate.load_witness(ctx, hi);
        range.range_check(ctx, &assigned_lo, 32);
        range.range_check(ctx, &assigned_hi, 32);
        let composed = gate.mul_add(
            ctx,
            QuantumCell::Existing(&assigned_hi),
            QuantumCell::Constant(F::from(1u64 << 32)),
            QuantumCell::Existing(&assigned_lo),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&r_spread),
            QuantumCell::Existing(&composed),
        );
        (assigned_lo, assigned_hi)
    };
    // println!(
    //     "r_spread {:?}, r_lo {:?}, r_hi {:?}",
    //     r_spread.value(),
    //     r_lo.value(),
    //     r_hi.value()
    // );
    let (r_lo_even, r_lo_odd) =
        spread_config.decompose_even_and_odd_unchecked(ctx, range, &r_lo)?;
    let (r_hi_even, r_hi_odd) =
        spread_config.decompose_even_and_odd_unchecked(ctx, range, &r_hi)?;
    // println!(
    //     "r_hi_even {:?}, r_lo_even {:?}",
    //     r_hi_even.value(),
    //     r_lo_even.value()
    // );
    {
        let even_spread = spread_config.spread(ctx, range, &r_lo_even)?;
        let odd_spread = spread_config.spread(ctx, range, &r_lo_odd)?;
        let sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(2)),
            QuantumCell::Existing(&odd_spread),
            QuantumCell::Existing(&even_spread),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&sum),
            QuantumCell::Existing(&r_lo),
        );
    }
    {
        let even_spread = spread_config.spread(ctx, range, &r_hi_even)?;
        let odd_spread = spread_config.spread(ctx, range, &r_hi_odd)?;
        let sum = gate.mul_add(
            ctx,
            QuantumCell::Constant(F::from(2)),
            QuantumCell::Existing(&odd_spread),
            QuantumCell::Existing(&even_spread),
        );
        gate.assert_equal(
            ctx,
            QuantumCell::Existing(&sum),
            QuantumCell::Existing(&r_hi),
        );
    }
    let r = gate.mul_add(
        ctx,
        QuantumCell::Existing(&r_hi_even),
        QuantumCell::Constant(F::from(1 << 16)),
        QuantumCell::Existing(&r_lo_even),
    );
    // println!("r {:?}", r.value());
    Ok(r)
}

// fn sigma_s_generic<'a, 'b: 'a, F: FieldExt>(
//     ctx: &mut Context<'b, F>,
//     gate: &FlexGateConfig<F>,
//     x_bits: &[AssignedValue<'a, F>],
//     n1: usize,
//     n2: usize,
//     n3: usize,
// ) -> Vec<AssignedValue<'a, F>> {
//     let rotr1 = rotr(ctx, gate, x_bits, n1);
//     let rotr2 = rotr(ctx, gate, x_bits, n2);
//     let shr = shr(ctx, gate, x_bits, n3);
//     rotr1
//         .iter()
//         .zip(rotr2.iter())
//         .zip(shr.iter())
//         .map(|((a, b), c)| xor3(ctx, gate, a, b, c))
//         .collect_vec()
// }

// fn rotr<'a, 'b: 'a, F: FieldExt>(
//     ctx: &mut Context<'b, F>,
//     gate: &FlexGateConfig<F>,
//     x_bits: &[AssignedValue<'a, F>],
//     n: usize,
// ) -> Vec<AssignedValue<'a, F>> {
//     debug_assert_eq!(x_bits.len(), 32);
//     // reference: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/rotate.circom
//     (0..32)
//         .map(|idx| x_bits[(idx + n) % 32].clone())
//         .collect_vec()
// }

// fn shr<'a, 'b: 'a, F: FieldExt>(
//     ctx: &mut Context<'b, F>,
//     gate: &FlexGateConfig<F>,
//     x_bits: &[AssignedValue<'a, F>],
//     n: usize,
// ) -> Vec<AssignedValue<'a, F>> {
//     debug_assert_eq!(x_bits.len(), 32);
//     // referece: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/shift.circom
//     let zero = gate.load_zero(ctx);
//     (0..32)
//         .map(|idx| {
//             if idx + n >= 32 {
//                 zero.clone()
//             } else {
//                 x_bits[idx + n].clone()
//             }
//         })
//         .collect_vec()
// }

// fn left_shift<'a, 'b: 'a, F: FieldExt>(
//     ctx: &mut Context<'b, F>,
//     gate: &FlexGateConfig<F>,
//     x_bits: &[AssignedValue<'a, F>],
//     n: usize,
// ) -> Vec<AssignedValue<'a, F>> {
//     debug_assert_eq!(x_bits.len(), 32);
//     let zero = gate.load_zero(ctx);
//     let padding = (0..n).map(|_| zero.clone()).collect_vec();
//     vec![&x_bits[n..32], &padding].concat()
// }

// fn xor3<'a, 'b: 'a, F: FieldExt>(
//     ctx: &mut Context<'b, F>,
//     gate: &FlexGateConfig<F>,
//     a: &AssignedValue<'a, F>,
//     b: &AssignedValue<'a, F>,
//     c: &AssignedValue<'a, F>,
// ) -> AssignedValue<'a, F> {
//     // referece: https://github.com/iden3/circomlib/blob/v0.2.4/circuits/sha256/xor3.circom
//     let mid = gate.mul(ctx, QuantumCell::Existing(&b), QuantumCell::Existing(&c));
//     let mid_term = gate.mul_add(
//         ctx,
//         QuantumCell::Existing(&b),
//         QuantumCell::Constant(-F::from(2u64)),
//         QuantumCell::Constant(F::from(1u64)),
//     );
//     let mid_term = gate.mul_add(
//         ctx,
//         QuantumCell::Existing(&c),
//         QuantumCell::Constant(-F::from(2u64)),
//         QuantumCell::Existing(&mid_term),
//     );
//     let mid_term = gate.mul_add(
//         ctx,
//         QuantumCell::Existing(&mid),
//         QuantumCell::Constant(F::from(4u64)),
//         QuantumCell::Existing(&mid_term),
//     );
//     let b_c = gate.add(ctx, QuantumCell::Existing(&b), QuantumCell::Existing(&c));
//     let add_term = gate.mul_add(
//         ctx,
//         QuantumCell::Existing(&mid),
//         QuantumCell::Constant(-F::from(2u64)),
//         QuantumCell::Existing(&b_c),
//     );
//     gate.mul_add(
//         ctx,
//         QuantumCell::Existing(&a),
//         QuantumCell::Existing(&mid_term),
//         QuantumCell::Existing(&add_term),
//     )
// }

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
