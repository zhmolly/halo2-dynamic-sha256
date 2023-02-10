// //! Gadget and chips for the [SHA-256] hash function.
// //!
// //! [SHA-256]: https://tools.ietf.org/html/rfc6234
use eth_types::Field;
use halo2wrong::halo2::{
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector, VirtualCells,
    },
    poly::Rotation,
};
use maingate::{
    big_to_fe, decompose_big, fe_to_big, AssignedValue, MainGate, MainGateConfig,
    MainGateInstructions, RangeChip, RangeConfig, RangeInstructions, RegionCtx,
};
use sha2::{Digest, Sha256};
use zkevm_circuits::sha256_circuit::sha256_bit::{Sha256BitChip, Sha256BitConfig};

const Sha256BitChipRowPerRound: usize = 72;
const BLOCK_BYTE: usize = 64;
const DIGEST_BYTE: usize = 32;
#[derive(Debug, Clone)]
pub struct Sha256DynamicConfig<F: Field> {
    sha256_bit_config: Sha256BitConfig<F>,
    max_byte_size: usize,
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
    // q_enable: Column<Fixed>,
    // q_first: Column<Fixed>,
    // q_input_word: Column<Fixed>,
    // q_hash: Column<Fixed>,
    // input_bytes: Column<Advice>,
    // length_acc: Column<Advice>,
    // hash_bytes: Column<Advice>,
    // is_actual: Column<Advice>,
}

#[derive(Debug, Clone)]
pub struct Sha256DynamicChip<F: Field> {
    pub config: Sha256DynamicConfig<F>,
}

impl<F: Field> Sha256DynamicConfig<F> {
    pub fn new(
        main_gate_config: MainGateConfig,
        range_config: RangeConfig,
        sha256_bit_config: Sha256BitConfig<F>,
        max_byte_size: usize,
    ) -> Self {
        Self {
            main_gate_config,
            range_config,
            sha256_bit_config,
            max_byte_size,
        }
    }

    // pub fn configure(meta: &mut ConstraintSystem<F>, max_byte_size: usize) -> Self {
    //     assert_eq!(max_byte_size % BLOCK_BYTE, 0);
    //     let sha256_bit_config = Sha256BitConfig::<F>::configure(meta);
    //     let q_enable = meta.fixed_column();
    //     let q_first = meta.fixed_column();
    //     let q_hash = meta.fixed_column();
    //     let input_bytes = meta.advice_column();
    //     meta.enable_equality(input_bytes);
    //     let length_acc = meta.advice_column();
    //     let hash_bytes = meta.advice_column();
    //     meta.enable_equality(hash_bytes);
    //     let is_actual = meta.advice_column();

    //     // meta.create_gate("input rlc check", |meta| {
    //     //     let q_enable = meta.query_fixed(q_enable, Rotation::cur());
    //     //     let q_first = meta.query_fixed(q_first, Rotation::cur());
    //     //     let input_byte = meta.query_advice(input_bytes, Rotation::cur());
    //     //     let is_actual = meta.query_advice(is_actual, Rotation::cur());
    //     //     let one = Expression::Constant(F::one());
    //     //     // 1. If q_first == true, input_byte_rlc_cur == input_byte
    //     //     // 2. If q_first == false and q_enable == true, (if is_actual == true, input_byte_rlc_cur == input_byte_rlc_prev * r + input_byte, else input_byte_rlc_cur == input_byte_rlc_prev)
    //     //     vec![
    //     //         q_first.clone() * (input_byte_rlc_cur.clone() - input_byte.clone()),
    //     //         q_enable
    //     //             * (one.clone() - q_first)
    //     //             * (is_actual.clone()
    //     //                 * (input_byte_rlc_cur.clone()
    //     //                     - input_byte_rlc_prev.clone() * r
    //     //                     - input_byte.clone())
    //     //                 + (one - is_actual) * (input_byte_rlc_cur - input_byte_rlc_prev)),
    //     //     ]
    //     // });
    //     meta.create_gate("input words check", |meta| {
    //         let q_enable = meta.query_fixed(q_enable, Rotation::cur());
    //         let q_first = meta.query_fixed(q_first, Rotation::cur());
    //         let input_byte = meta.query_advice(input_bytes, Rotation::cur());
    //         let is_actual = meta.query_advice(is_actual, Rotation::cur());
    //         let one = Expression::Constant(F::one());
    //     });

    //     meta.create_gate("check is_actual and length_acc", |meta| {
    //         let q_enable = meta.query_fixed(q_enable, Rotation::cur());
    //         let q_first = meta.query_fixed(q_first, Rotation::cur());
    //         let is_actual_cur = meta.query_advice(is_actual, Rotation::cur());
    //         let is_actual_prev = meta.query_advice(is_actual, Rotation::prev());
    //         let is_actual_change_inv = is_actual_prev.clone() - is_actual_cur.clone();
    //         let length_acc_cur = meta.query_advice(length_acc, Rotation::cur());
    //         let length_acc_prev = meta.query_advice(length_acc, Rotation::prev());
    //         let length_change = length_acc_cur.clone() - length_acc_prev.clone();
    //         let one = Expression::Constant(F::one());
    //         let not_q_first = one.clone() - q_first.clone();
    //         vec![
    //             q_first.clone() * (is_actual_cur.clone() - one.clone()), // If q_first==true, is_actual_cur == 1
    //             q_first.clone() * (length_acc_cur.clone() - one.clone()), // If q_first==true, length_acc_cur == 1
    //             not_q_first.clone() // If q_first==false, is_actual_change_inv is either 0 or 1. (is_actual_cur == is_actual_prev or is_actual_prev - is_actual_cur = 1)
    //                 * q_enable.clone()
    //                 * is_actual_change_inv.clone()
    //                 * (one.clone() - is_actual_change_inv.clone()),
    //             not_q_first.clone()
    //                 * q_enable.clone()
    //                 * is_actual_cur.clone()
    //                 * (length_change.clone() - one.clone()), // If q_first==false and q_enable==true and is_actual_cur == true, length_acc_cur - length_acc_prev == 1
    //             not_q_first.clone()
    //                 * q_enable.clone()
    //                 * (one.clone() - is_actual_cur.clone())
    //                 * length_change, // If q_first==false and q_enable==true and is_actual_cur == false, length_acc_cur - length_acc_prev == 0
    //         ]
    //     });

    //     meta.create_gate("check hash bytes", |meta| {
    //         let q_enable = meta.query_fixed(q_enable, Rotation::cur());
    //         let q_first = meta.query_fixed(q_first, Rotation::cur());
    //         let q_hash = meta.query_fixed(q_hash, Rotation::cur());
    //         let hash_bytes = meta.query_advice(hash_bytes, Rotation::cur());
    //         let one = Expression::Constant(F::one());
    //         // 1. If q_first == true, hash_rlc_cur == hash_words
    //         // 2. If q_first == false and q_enable == true, (if q_hash == true, hash_rlc_cur == hash_rlc_prev * r + hash_words, else hash_rlc_cur == hash_rlc_prev)
    //         vec![
    //             q_first.clone() * (hash_rlc_cur.clone() - hash_bytes),
    //             q_enable
    //                 * (one.clone() - q_first)
    //                 * (q_hash.clone() * (hash_rlc_cur.clone() - rlc)
    //                     + (one - q_hash) * (hash_rlc_cur - hash_rlc_prev)),
    //         ]
    //     });

    //     meta.create_gate("hash table", |meta| {
    //         let table = sha256_bit_config.hash_table.clone();
    //         let is_enable_table = meta.query_advice(table.is_enabled, Rotation::cur());
    //         let length_table = meta.query_advice(table.input_len, Rotation::cur());
    //         let input_rlc_table = meta.query_advice(table.input_rlc, Rotation::cur());
    //         let output_rlc_table = meta.query_advice(table.output_rlc, Rotation::cur());
    //         let q_enable = meta.query_fixed(q_enable, Rotation::cur());
    //         let length_acc = meta.query_advice(length_acc, Rotation::cur());
    //         let input_byte_rlc = meta.query_advice(input_byte_rlc, Rotation::cur());
    //         let hash_rlc = meta.query_advice(hash_rlc, Rotation::cur());
    //         vec![
    //             q_enable.clone() * is_enable_table.clone() * (length_table - length_acc),
    //             q_enable.clone() * is_enable_table.clone() * (input_rlc_table - input_byte_rlc),
    //             q_enable.clone() * is_enable_table.clone() * (output_rlc_table - hash_rlc),
    //         ]
    //     });

    //     Self {
    //         sha256_bit_config,
    //         max_byte_size,
    //         q_enable,
    //         q_first,
    //         q_hash,
    //         input_bytes,
    //         input_byte_rlc,
    //         length_acc,
    //         hash_bytes,
    //         hash_rlc,
    //         is_actual,
    //     }
    // }
}

impl<F: Field> Sha256DynamicChip<F> {
    const NUM_LOOKUP_TABLES: usize = 8;

    pub fn new(config: Sha256DynamicConfig<F>) -> Self {
        Self { config }
    }

    pub fn compute_range_lens() -> (Vec<usize>, Vec<usize>) {
        let composition_bit_lens = vec![
            8 / Self::NUM_LOOKUP_TABLES,
            32 / Self::NUM_LOOKUP_TABLES,
            64 / Self::NUM_LOOKUP_TABLES,
        ];
        (composition_bit_lens, vec![])
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        max_byte_size: usize,
    ) -> Sha256DynamicConfig<F> {
        let main_gate_config = MainGate::configure(meta);

        let (composition_bit_lens, overflow_bit_lens) = Self::compute_range_lens();
        let range_config = RangeChip::configure(
            meta,
            &main_gate_config,
            composition_bit_lens,
            overflow_bit_lens,
        );
        let sha256_bit_config = Sha256BitConfig::configure(meta);
        Sha256DynamicConfig::new(
            main_gate_config,
            range_config,
            sha256_bit_config,
            max_byte_size,
        )
    }

    /// Getter for [`RangeChip`].
    pub fn range_chip(&self) -> RangeChip<F> {
        RangeChip::<F>::new(self.config.range_config.clone())
    }

    /// Getter for [`MainGate`].
    pub fn main_gate(&self) -> MainGate<F> {
        MainGate::<F>::new(self.config.main_gate_config.clone())
    }

    pub fn sha256_bit(&self) -> Sha256BitChip<F> {
        Sha256BitChip::new(
            self.config.sha256_bit_config.clone(),
            self.config.max_byte_size,
        )
    }

    pub fn digest(
        &self,
        mut layouter: impl Layouter<F>,
        input: &[u8],
    ) -> Result<
        (
            AssignedValue<F>,
            Vec<AssignedValue<F>>,
            Vec<AssignedValue<F>>,
        ),
        Error,
    > {
        let input_byte_size = input.len();
        assert!(input_byte_size <= self.config.max_byte_size);
        let main_gate = self.main_gate();
        let range_chip = self.range_chip();
        let sha256_bit_chip = self.sha256_bit();
        let hash = Sha256::digest(input);
        let assigned_rows = layouter.assign_region(
            || "assigned_rows",
            |mut region| sha256_bit_chip.digest(&mut region, input),
        )?;
        let (sum_input_len, assigned_input, sum_hash_bytes) = layouter.assign_region(
            || "assign outputs",
            |mut region| {
                let ctx = &mut RegionCtx::new(region, 0);

                let input_byte_size_with_9 = input_byte_size + 9;
                let one_round_size = BLOCK_BYTE;
                let num_round = if input_byte_size_with_9 % one_round_size == 0 {
                    input_byte_size_with_9 / one_round_size
                } else {
                    input_byte_size_with_9 / one_round_size + 1
                };
                let padded_size = one_round_size * num_round;
                let zero_padding_byte_size = padded_size - input_byte_size - 9;
                let max_byte_size = self.config.max_byte_size;
                let max_round = max_byte_size / one_round_size;
                let remaining_byte_size = max_byte_size - padded_size;
                assert_eq!(
                    remaining_byte_size,
                    one_round_size * (max_round - num_round)
                );

                // let mut padded_inputs = input.to_vec();
                // padded_inputs.push(0x80);
                // for _ in 0..zero_padding_byte_size {
                //     padded_inputs.push(0);
                // }
                // let mut input_len_bytes = [0; 8];
                // let le_size_bytes = (8 * input_byte_size).to_le_bytes();
                // input_len_bytes[0..le_size_bytes.len()].copy_from_slice(&le_size_bytes);
                // for byte in input_len_bytes.iter().rev() {
                //     padded_inputs.push(*byte);
                // }
                // assert_eq!(padded_inputs.len(), num_round * one_round_size);
                // for _ in 0..remaining_byte_size {
                //     padded_inputs.push(0);
                // }
                // assert_eq!(padded_inputs.len(), max_byte_size);

                let zero = main_gate.assign_constant(ctx, F::zero())?;

                let mut assigned_input = vec![];
                for byte in input.iter() {
                    assigned_input.push(range_chip.assign(
                        ctx,
                        Value::known(F::from(*byte as u64)),
                        8 / Self::NUM_LOOKUP_TABLES,
                        8,
                    )?);
                }
                assigned_input.push(main_gate.assign_constant(ctx, F::from(0x80))?);
                for _ in 0..zero_padding_byte_size {
                    assigned_input.push(zero.clone());
                }
                let mut input_len_bytes = [0; 8];
                let le_size_bytes = (8 * input_byte_size).to_le_bytes();
                input_len_bytes[0..le_size_bytes.len()].copy_from_slice(&le_size_bytes);
                for byte in input_len_bytes.iter().rev() {
                    assigned_input
                        .push(main_gate.assign_value(ctx, Value::known(F::from(*byte as u64)))?);
                }
                assert_eq!(assigned_input.len(), num_round * one_round_size);
                for _ in 0..remaining_byte_size {
                    assigned_input.push(zero.clone());
                }
                assert_eq!(assigned_input.len(), max_byte_size);

                let mut sum_input_len = zero.clone();
                let mut sum_hash_bytes = vec![zero.clone(); 32];
                for round_idx in 0..max_round {
                    let input_len = &assigned_rows.input_len[round_idx];
                    let input_words =
                        assigned_rows.input_words[16 * round_idx..16 * (round_idx + 1)].to_vec();
                    let is_output_enabled = &assigned_rows.is_output_enabled[round_idx];
                    let output_words =
                        assigned_rows.output_words[4 * round_idx..4 * round_idx + 4].to_vec();
                    //let is_dummy = &assigned_rows.is_dummy[round_idx];

                    sum_input_len = {
                        let muled = main_gate.mul(ctx, &is_output_enabled, &input_len)?;
                        main_gate.add(ctx, &sum_input_len, &muled)?
                    };

                    for word_idx in 0..16 {
                        let offset_in = 64 * round_idx + 4 * word_idx;
                        let assigned_input_u32 =
                            assigned_input[offset_in + 0..offset_in + 4].to_vec();
                        let mut sum = zero.clone();
                        for (idx, assigned_byte) in assigned_input_u32.iter().enumerate() {
                            let coeff =
                                main_gate.assign_constant(ctx, F::from_u128(1u128 << (8 * idx)))?;
                            let mul = main_gate.mul(ctx, assigned_byte, &coeff)?;
                            sum = main_gate.add(ctx, &sum, &mul)?;
                        }
                        main_gate.assert_equal(ctx, &sum, &input_words[word_idx])?;
                    }

                    for word_idx in 0..4 {
                        let hash_bytes_val = (0..8)
                            .map(|idx| {
                                output_words[word_idx]
                                    .value()
                                    .map(|v| {
                                        (v.get_lower_128() >> (8 * idx)) & ((1u128 << 8) - 1u128)
                                    })
                                    .map(|v| F::from_u128(v))
                            })
                            .collect::<Vec<Value<F>>>();
                        let assigned_hash_bytes = hash_bytes_val
                            .iter()
                            .map(|v| range_chip.assign(ctx, *v, 8 / Self::NUM_LOOKUP_TABLES, 8))
                            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
                        let mut sum = zero.clone();
                        for (idx, assigned_byte) in assigned_hash_bytes.iter().enumerate() {
                            let coeff = main_gate.assign_constant(ctx, F::from(1 << (8 * idx)))?;
                            let mul = main_gate.mul(ctx, assigned_byte, &coeff)?;
                            sum = main_gate.add(ctx, &sum, &mul)?;
                        }
                        main_gate.assert_equal(ctx, &sum, &output_words[word_idx])?;
                        for idx in 0..8 {
                            let mul = main_gate.mul(
                                ctx,
                                &is_output_enabled,
                                &assigned_hash_bytes[idx],
                            )?;
                            sum_hash_bytes[8 * word_idx + idx] =
                                main_gate.add(ctx, &sum_hash_bytes[8 * word_idx + idx], &mul)?;
                        }
                    }
                }
                Ok((sum_input_len, assigned_input, sum_hash_bytes))
            },
        )?;

        Ok((sum_input_len, assigned_input, sum_hash_bytes))

        // let first_r = sha256_bit_chip.digest(region, inputs, r)?;
        // region.assign_fixed(
        //     || "assign q_first at 0",
        //     self.config.q_first,
        //     0,
        //     || Value::known(F::one()),
        // )?;
        // for idx in 1..self.config.max_byte_size {
        //     region.assign_fixed(
        //         || format!("assign q_first at {}", idx),
        //         self.config.q_first,
        //         idx,
        //         || Value::known(F::zero()),
        //     )?;
        // }
        // for idx in 0..self.config.max_byte_size {
        //     region.assign_fixed(
        //         || format!("assign q_enable at {}", idx),
        //         self.config.q_enable,
        //         idx,
        //         || Value::known(F::one()),
        //     )?;
        // }
        // for idx in 0..DIGEST_BYTE {
        //     region.assign_fixed(
        //         || format!("assign q_hash at {}", idx),
        //         self.config.q_hash,
        //         idx,
        //         || Value::known(F::one()),
        //     )?;
        // }

        // let assigned_inputs = (0..self.config.max_byte_size)
        //     .map(|idx| {
        //         let val = if idx < input_byte_size {
        //             F::from_u128(inputs[idx] as u128)
        //         } else {
        //             F::zero()
        //         };
        //         region.assign_advice(
        //             || format!("input byte at {}", idx),
        //             self.config.input_bytes,
        //             idx,
        //             || Value::known(val),
        //         )
        //     })
        //     .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        // region.assign_advice(
        //     || format!("input byte rlc at {}", 0),
        //     self.config.input_byte_rlc,
        //     0,
        //     || Value::known(F::from_u128(inputs[0] as u128)),
        // )?;
        // let mut input_rlc = F::from_u128(inputs[0] as u128);
        // for idx in 0..self.config.max_byte_size {
        //     region.assign_advice(
        //         || format!("input byte rlc at {}", idx),
        //         self.config.input_byte_rlc,
        //         idx,
        //         || Value::known(input_rlc.clone()),
        //     )?;
        //     if idx < input_byte_size - 1 {
        //         input_rlc = input_rlc * r + F::from_u128(inputs[idx + 1] as u128);
        //     }
        // }
        // let assigned_hash = hash
        //     .iter()
        //     .rev()
        //     .enumerate()
        //     .map(|(idx, byte)| {
        //         region.assign_advice(
        //             || format!("hash byte at {}", idx),
        //             self.config.hash_bytes,
        //             idx,
        //             || Value::known(F::from(*byte as u64)),
        //         )
        //     })
        //     .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;

        // let mut hash_rlc = F::zero();
        // for (idx, byte) in hash.iter().rev().enumerate() {
        //     hash_rlc = hash_rlc * r + F::from(*byte as u64);
        //     region.assign_advice(
        //         || format!("hash byte rlc at {}", idx),
        //         self.config.hash_rlc,
        //         idx,
        //         || Value::known(hash_rlc.clone()),
        //     )?;
        // }
        // for idx in DIGEST_BYTE..self.config.max_byte_size {
        //     region.assign_advice(
        //         || format!("hash byte rlc at {}", idx),
        //         self.config.hash_rlc,
        //         idx,
        //         || Value::known(hash_rlc.clone()),
        //     )?;
        // }
        // // for idx in 0..self.config.max_byte_size {
        // //     region.assign_advice(
        // //         || format!("hash byte rlc at {}", idx),
        // //         self.config.hash_rlc,
        // //         idx,
        // //         || Value::known(hash_rlc.clone()),
        // //     )?;
        // //     if idx < DIGEST_BYTE-1  {
        // //         hash_rlc = hash_rlc * r + F::from_u128(hash[idx+1] as u128);
        // //         println!("idx {}, hash_rlc {:?}",idx,hash_rlc);
        // //     }
        // // }

        // for idx in 0..self.config.max_byte_size {
        //     let (len_acc, is_actual) = if idx < input_byte_size {
        //         ((idx + 1) as u128, F::one())
        //     } else {
        //         (input_byte_size as u128, F::zero())
        //     };
        //     region.assign_advice(
        //         || format!("length acc at {}", idx),
        //         self.config.length_acc,
        //         idx,
        //         || Value::known(F::from_u128(len_acc)),
        //     )?;
        //     region.assign_advice(
        //         || format!("is_actual at {}", idx),
        //         self.config.is_actual,
        //         idx,
        //         || Value::known(is_actual),
        //     )?;
        // }
        // Ok((first_r, assigned_inputs, assigned_hash))
    }

    // fn is_less_than_u64(
    //     &self,
    //     ctx: &mut RegionCtx<F>,
    //     a: &AssignedValue<F>,
    //     b: &AssignedValue<F>,
    // ) -> Result<AssignedValue<F>, Error> {
    //     let main_gate = self.main_gate();
    //     let inflated_a = main_gate.add_constant(ctx, a, F::from_u128(1 << 64))?;
    //     let sub = main_gate.sub(ctx, &inflated_a, b)?;
    //     let sub_bits = main_gate.to_bits(ctx, &sub, 65)?;
    //     let is_overflow = main_gate.is_zero(ctx, &sub_bits[64])?;
    //     let is_eq = main_gate.is_equal(ctx, a, b)?;
    //     let is_not_eq = main_gate.not(ctx, &is_eq)?;
    //     let is_less = main_gate.and(ctx, &is_overflow, &is_not_eq)?;
    //     Ok(is_less)
    // }
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use super::*;
    use eth_types::Field;
    use halo2wrong::curves::pasta::pallas;
    use halo2wrong::halo2::plonk::Advice;
    use halo2wrong::halo2::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        plonk::{
            create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, Column, ConstraintSystem,
            Error, Instance,
        },
        poly::commitment::Params,
        transcript::{Blake2bRead, Blake2bWrite, Challenge255},
    };
    use halo2wrong::utils::fe_to_big;
    use rand::rngs::OsRng;

    #[derive(Debug, Clone)]
    struct TestConfig<F: Field> {
        sha256_config: Sha256DynamicConfig<F>,
        //hash_instance: Column<Instance>,
    }

    #[derive(Debug, Clone)]
    struct TestCircuit<F: Field> {
        test_input: Vec<u8>,
        _f: PhantomData<F>,
    }

    impl<F: Field> Circuit<F> for TestCircuit<F> {
        type Config = TestConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let sha256_config = Sha256DynamicChip::configure(meta, Self::MAX_BYTE_SIZE);
            //let hash_instance = meta.instance_column();
            //meta.enable_equality(hash_instance);
            Self::Config { sha256_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let sha256_chip = Sha256DynamicChip::new(config.sha256_config.clone());
            let range_chip = sha256_chip.range_chip();
            range_chip.load_table(&mut layouter)?;
            let (_, _, assigned_hash) = sha256_chip.digest(
                layouter.namespace(|| "sha256_dynamic_chip"),
                &self.test_input,
            )?;
            let maingate = sha256_chip.main_gate();
            for (idx, cell) in assigned_hash.into_iter().enumerate() {
                maingate.expose_public(layouter.namespace(|| "expose hash"), cell, idx)?;
            }
            Ok(())
        }
    }

    impl<F: Field> TestCircuit<F> {
        const MAX_BYTE_SIZE: usize = 128;
    }

    use halo2wrong::curves::bn256::Fr;
    use halo2wrong::halo2::arithmetic::FieldExt;
    use halo2wrong::halo2::dev::MockProver;
    use rand::{thread_rng, Rng};
    #[test]
    fn test_sha256_correct1() {
        let k = 10;

        // Test vector: "abc"
        let test_input = vec!['a' as u8, 'b' as u8, 'c' as u8];

        // let rng = thread_rng();
        // let r = <Fr as halo2wrong::halo2::arithmetic::Field>::random(rng);

        let circuit = TestCircuit::<Fr> {
            test_input,
            _f: PhantomData,
        };
        let test_output: [u8; 32] = /*[
            0b10111010011110000001011010111111,
            0b10001111000000011100111111101010,
            0b01000001010000010100000011011110,
            0b01011101101011100010001000100011,
            0b10110000000000110110000110100011,
            0b10010110000101110111101010011100,
            0b10110100000100001111111101100001,
            0b11110010000000000001010110101101,
        ];*/
        [
            0b10111010, 0b01111000, 0b00010110, 0b10111111, 0b10001111, 0b00000001, 0b11001111,
            0b11101010, 0b01000001, 0b01000001, 0b01000000, 0b11011110, 0b01011101, 0b10101110,
            0b00100010, 0b00100011, 0b10110000, 0b00000011, 0b01100001, 0b10100011, 0b10010110,
            0b00010111, 0b01111010, 0b10011100, 0b10110100, 0b00010000, 0b11111111, 0b01100001,
            0b11110010, 0b00000000, 0b00010101, 0b10101101,
        ];
        let test_output = test_output.map(|val| Fr::from_u128(val as u128)).to_vec();
        let public_inputs = vec![test_output];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_sha256_correct2() {
        let k = 10;

        let rng = thread_rng();
        let r = <Fr as halo2wrong::halo2::arithmetic::Field>::random(rng);

        // Test vector: "0x0"
        let test_input = vec![0u8];

        let circuit = TestCircuit::<Fr> {
            test_input,
            _f: PhantomData,
        };
        let test_output: [u8; 32] = [
            0x6e, 0x34, 0x0b, 0x9c, 0xff, 0xb3, 0x7a, 0x98, 0x9c, 0xa5, 0x44, 0xe6, 0xbb, 0x78,
            0x0a, 0x2c, 0x78, 0x90, 0x1d, 0x3f, 0xb3, 0x37, 0x38, 0x76, 0x85, 0x11, 0xa3, 0x06,
            0x17, 0xaf, 0xa0, 0x1d,
        ];
        let test_output = test_output.map(|val| Fr::from_u128(val as u128)).to_vec();
        let public_inputs = vec![test_output];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_sha256_correct3() {
        let k = 10;

        let test_input = vec![0x1; 60];

        let circuit = TestCircuit::<Fr> {
            test_input,
            _f: PhantomData,
        };
        let test_output: [u8; 32] = [
            0x5e, 0x40, 0x84, 0xef, 0xf2, 0xf3, 0x7d, 0x63, 0x7e, 0x65, 0x02, 0xbf, 0x94, 0x72,
            0xb0, 0x02, 0x97, 0x55, 0xbb, 0xd1, 0x30, 0xeb, 0xb5, 0x2c, 0x8c, 0x33, 0xbb, 0x81,
            0x48, 0xc3, 0x1f, 0xd2,
        ];
        let test_output = test_output.map(|val| Fr::from_u128(val as u128)).to_vec();
        let public_inputs = vec![test_output];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
