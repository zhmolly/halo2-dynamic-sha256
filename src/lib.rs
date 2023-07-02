mod compression;
pub(crate) mod spread;
pub(crate) mod utils;
pub use compression::*;
// pub use eth_types::Field;
// pub use zkevm_circuits::sha256_circuit::{
//     sha256_compression::{Sha256AssignedRows, Sha256CompressionConfig},
//     util::H,
// };

use generic_array::GenericArray;
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
use sha2::{compress256, Digest, Sha256};
use spread::SpreadConfig;

// const Sha256BitChipRowPerRound: usize = 72;
// const BLOCK_BYTE: usize = 64;
// const DIGEST_BYTE: usize = 32;

#[derive(Debug, Clone)]
pub struct AssignedHashResult<'a, F: PrimeField> {
    pub input_len: AssignedValue<'a, F>,
    pub input_bytes: Vec<AssignedValue<'a, F>>,
    pub output_bytes: Vec<AssignedValue<'a, F>>,
}

#[derive(Debug, Clone)]
pub struct Sha256DynamicConfig<F: PrimeField> {
    pub max_variable_byte_sizes: Vec<usize>,
    range: RangeConfig<F>,
    spread_config: SpreadConfig<F>,
    pub cur_hash_idx: usize,
    is_input_range_check: bool,
}

impl<F: PrimeField> Sha256DynamicConfig<F> {
    const ONE_ROUND_INPUT_BYTES: usize = 64;
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        max_variable_byte_sizes: Vec<usize>,
        range: RangeConfig<F>,
        num_bits_lookup: usize,
        num_advice_columns: usize,
        is_input_range_check: bool,
    ) -> Self {
        for byte in max_variable_byte_sizes.iter() {
            debug_assert_eq!(byte % Self::ONE_ROUND_INPUT_BYTES, 0);
        }
        // let max_byte_sum = max_byte_sizes.iter().sum::<usize>();
        let spread_config = SpreadConfig::configure(meta, num_bits_lookup, num_advice_columns);
        Self {
            max_variable_byte_sizes,
            range,
            spread_config,
            cur_hash_idx: 0,
            is_input_range_check,
        }
    }

    pub fn digest<'a, 'b: 'a>(
        &'a mut self,
        ctx: &mut Context<'b, F>,
        input: &'a [u8],
        precomputed_input_len: Option<usize>,
    ) -> Result<AssignedHashResult<'b, F>, Error> {
        let input_byte_size = input.len();
        let input_byte_size_with_9 = input_byte_size + 9;
        let one_round_size = Self::ONE_ROUND_INPUT_BYTES;
        let num_round = if input_byte_size_with_9 % one_round_size == 0 {
            input_byte_size_with_9 / one_round_size
        } else {
            input_byte_size_with_9 / one_round_size + 1
        };
        let padded_size = one_round_size * num_round;
        let max_variable_byte_size = self.max_variable_byte_sizes[self.cur_hash_idx];
        let max_variable_round = max_variable_byte_size / one_round_size;
        let precomputed_input_len = precomputed_input_len.unwrap_or(0);
        assert_eq!(precomputed_input_len % one_round_size, 0);
        assert!(padded_size - precomputed_input_len <= max_variable_byte_size);
        let zero_padding_byte_size = padded_size - input_byte_size_with_9;
        let remaining_byte_size = max_variable_byte_size + precomputed_input_len - padded_size;
        let precomputed_round = precomputed_input_len / one_round_size;
        assert_eq!(
            remaining_byte_size,
            one_round_size * (max_variable_round + precomputed_round - num_round)
        );
        let mut padded_inputs = input.to_vec();
        padded_inputs.push(0x80);
        for _ in 0..zero_padding_byte_size {
            padded_inputs.push(0);
        }
        let mut input_len_bytes = [0; 8];
        let le_size_bytes = (8 * input_byte_size).to_le_bytes();
        input_len_bytes[0..le_size_bytes.len()].copy_from_slice(&le_size_bytes);
        for byte in input_len_bytes.iter().rev() {
            padded_inputs.push(*byte);
        }

        assert_eq!(padded_inputs.len(), num_round * one_round_size);
        for _ in 0..remaining_byte_size {
            padded_inputs.push(0);
        }
        assert_eq!(
            padded_inputs.len(),
            max_variable_byte_size + precomputed_input_len
        );
        // for (idx, byte) in padded_inputs.iter().enumerate() {
        //     println!("idx {} byte {}", idx, byte);
        // }

        let range = self.range().clone();
        let gate = range.gate();
        let assigned_input_byte_size =
            gate.load_witness(ctx, Value::known(F::from(input_byte_size as u64)));
        let assigned_num_round = gate.load_witness(ctx, Value::known(F::from(num_round as u64)));
        let assigned_padded_size = gate.mul(
            ctx,
            QuantumCell::Existing(&assigned_num_round),
            QuantumCell::Constant(F::from(one_round_size as u64)),
        );
        let assigned_input_with_9_size = gate.add(
            ctx,
            QuantumCell::Existing(&assigned_input_byte_size),
            QuantumCell::Constant(F::from(9u64)),
        );
        let padding_size = gate.sub(
            ctx,
            QuantumCell::Existing(&assigned_padded_size),
            QuantumCell::Existing(&assigned_input_with_9_size),
        );
        let padding_is_less_than_round =
            range.is_less_than_safe(ctx, &padding_size, one_round_size as u64);
        gate.assert_is_const(ctx, &padding_is_less_than_round, F::one());
        let assigned_precomputed_round =
            gate.load_witness(ctx, Value::known(F::from(precomputed_round as u64)));
        let assigned_target_round = gate.sub(
            ctx,
            QuantumCell::Existing(&assigned_num_round),
            QuantumCell::Existing(&assigned_precomputed_round),
        );

        // compute an initial state from the precomputed_input.
        let precomputed_input = &padded_inputs[0..precomputed_input_len];
        let mut last_state = INIT_STATE;
        let precomputed_blocks = precomputed_input
            .chunks(one_round_size)
            .map(|bytes| GenericArray::clone_from_slice(bytes))
            .collect_vec();
        compress256(&mut last_state, &precomputed_blocks[..]);

        let mut assigned_last_state_vec = vec![last_state
            .iter()
            .map(|state| gate.load_witness(ctx, Value::known(F::from(*state as u64))))
            .collect_vec()];
        // vec![INIT_STATE
        //     .iter()
        //     .map(|h| gate.load_constant(ctx, F::from(*h as u64)))
        //     .collect::<Vec<AssignedValue<F>>>()];
        let assigned_input_bytes = padded_inputs[precomputed_input_len..]
            .iter()
            .map(|byte| gate.load_witness(ctx, Value::known(F::from(*byte as u64))))
            .collect::<Vec<AssignedValue<F>>>();
        if self.is_input_range_check {
            for assigned_byte in assigned_input_bytes.iter() {
                range.range_check(ctx, assigned_byte, 8);
            }
        }
        let mut num_processed_input = 0;
        while num_processed_input < max_variable_byte_size {
            let assigned_input_word_at_round =
                &assigned_input_bytes[num_processed_input..(num_processed_input + one_round_size)];
            let new_assigned_hs_out = sha256_compression(
                ctx,
                &range,
                &mut self.spread_config,
                assigned_input_word_at_round,
                &assigned_last_state_vec.last().unwrap(),
            )?;

            // let (witness, next_hs) = sha2_comp_config.compute_witness(
            //     &padded_inputs[num_processed_input..(num_processed_input + one_round_size)],
            //     last_hs,
            // );

            // last_hs = next_hs;
            // let mut assigned_rows: Sha256AssignedRows<F> =
            //     Sha256AssignedRows::<F>::new(self.num_consumed_rows);
            // sha2_comp_config.assign_witness(&mut ctx.region, &witness, &mut assigned_rows)?;
            // let assigned_h_ins: Vec<Vec<AssignedCell<F, F>>> = assigned_rows.get_h_ins();
            // debug_assert_eq!(assigned_h_ins.len(), 1);
            // let assigned_h_outs: Vec<Vec<AssignedCell<F, F>>> = assigned_rows.get_h_outs();
            // debug_assert_eq!(assigned_h_outs.len(), 1);
            // let assigned_input_words = assigned_rows.get_input_words();
            // debug_assert_eq!(assigned_input_words.len(), 1);

            // 1. Constrain input bytes.
            // for word_idx in 0..16 {
            //     let assigned_input_u32 =
            //         &assigned_input_word_at_round[4 * word_idx..4 * (word_idx + 1)];
            //     let mut sum = gate.load_zero(ctx);
            //     for (idx, assigned_byte) in assigned_input_u32.iter().enumerate() {
            //         sum = gate.mul_add(
            //             ctx,
            //             QuantumCell::Existing(assigned_byte),
            //             QuantumCell::Constant(F::from(1u64 << (8 * idx))),
            //             QuantumCell::Existing(&sum),
            //         );
            //     }
            //     ctx.region
            //         .constrain_equal(sum.cell(), assigned_input_words[0][word_idx].cell())?;
            // }
            // 2. Constrain the previous h_out == current h_in.
            // for (h_out, h_in) in assigned_last_hs_vec[assigned_last_hs_vec.len() - 1]
            //     .iter()
            //     .zip(assigned_h_ins[0].iter())
            // {
            //     ctx.region.constrain_equal(h_out.cell(), h_in.cell())?;
            // }
            // 3. Push the current h_out to assigned_last_hs_vec.
            // let mut new_assigned_hs_out = vec![];
            // for h_out in assigned_h_outs[0].iter() {
            //     let assigned_on_gate = self.assigned_cell2value(ctx, h_out)?;
            //     new_assigned_hs_out.push(assigned_on_gate)
            // }
            assigned_last_state_vec.push(new_assigned_hs_out);
            num_processed_input += one_round_size;
        }

        // for n_column in 0..num_column {
        //     let sha2_comp_config = &self.sha256_comp_configs[n_column];
        //     for n_round in 0..num_round_per_column {
        //         let round_idx = n_column * num_round_per_column + n_round;
        //         let (witness, next_hs) = sha2_comp_config.compute_witness(
        //             &padded_inputs[round_idx * one_round_size..(round_idx + 1) * one_round_size],
        //             last_hs,
        //         );
        //         last_hs = next_hs;
        //         let mut assigned_rows = Sha256AssignedRows::<F>::new(
        //             n_round * Sha256CompressionConfig::<F>::ROWS_PER_BLOCK,
        //         );
        //         sha2_comp_config.assign_witness(&mut ctx.region, &witness, &mut assigned_rows)?;
        //         let assigned_h_ins = assigned_rows.get_h_ins();
        //         debug_assert_eq!(assigned_h_ins.len(), 1);
        //         let assigned_h_outs = assigned_rows.get_h_outs();
        //         debug_assert_eq!(assigned_h_outs.len(), 1);
        //         let assigned_input_words = assigned_rows.get_input_words();
        //         debug_assert_eq!(assigned_input_words.len(), 1);
        //         let assigned_input_word_at_round = &assigned_input_bytes
        //             [round_idx * one_round_size..(round_idx + 1) * one_round_size];
        //         // 1. Constrain input bytes.
        //         for word_idx in 0..16 {
        //             let assigned_input_u32 =
        //                 &assigned_input_word_at_round[4 * word_idx..4 * (word_idx + 1)];
        //             let mut sum = gate.load_zero(ctx);
        //             for (idx, assigned_byte) in assigned_input_u32.iter().enumerate() {
        //                 sum = gate.mul_add(
        //                     ctx,
        //                     QuantumCell::Existing(assigned_byte),
        //                     QuantumCell::Constant(F::from(1u64 << (8 * idx))),
        //                     QuantumCell::Existing(&sum),
        //                 );
        //             }
        //             ctx.region
        //                 .constrain_equal(sum.cell(), assigned_input_words[0][word_idx].cell())?;
        //         }
        //         // 2. Constrain the previous h_out == current h_in.
        //         for (h_out, h_in) in assigned_last_hs_vec[assigned_last_hs_vec.len() - 1]
        //             .iter()
        //             .zip(assigned_h_ins[0].iter())
        //         {
        //             ctx.region.constrain_equal(h_out.cell(), h_in.cell())?;
        //         }
        //         // 3. Push the current h_out to assigned_last_hs_vec.
        //         let mut new_assigned_hs_out = vec![];
        //         for h_out in assigned_h_outs[0].iter() {
        //             let assigned_on_gate = self.assigned_cell2value(ctx, h_out)?;
        //             new_assigned_hs_out.push(assigned_on_gate)
        //         }
        //         assigned_last_hs_vec.push(new_assigned_hs_out);
        //     }
        // }

        let zero = gate.load_zero(ctx);
        let mut output_h_out = vec![zero; 8];
        for (n_round, assigned_state) in assigned_last_state_vec.into_iter().enumerate() {
            let selector = gate.is_equal(
                ctx,
                QuantumCell::Constant(F::from(n_round as u64)),
                QuantumCell::Existing(&assigned_target_round),
            );
            for i in 0..8 {
                output_h_out[i] = gate.select(
                    ctx,
                    QuantumCell::Existing(&assigned_state[i]),
                    QuantumCell::Existing(&output_h_out[i]),
                    QuantumCell::Existing(&selector),
                )
            }
        }
        let output_digest_bytes = output_h_out
            .into_iter()
            .flat_map(|assigned_word| {
                let be_bytes = assigned_word
                    .value()
                    .map(|v| v.get_lower_32().to_be_bytes().to_vec());
                let assigned_bytes = (0..4)
                    .map(|idx| {
                        let assigned = gate
                            .load_witness(ctx, be_bytes.as_ref().map(|vs| F::from(vs[idx] as u64)));
                        range.range_check(ctx, &assigned, 8);
                        assigned
                    })
                    .collect::<Vec<AssignedValue<F>>>();
                let mut sum = gate.load_zero(ctx);
                for (idx, assigned_byte) in assigned_bytes.iter().enumerate() {
                    sum = gate.mul_add(
                        ctx,
                        QuantumCell::Existing(assigned_byte),
                        QuantumCell::Constant(F::from(1u64 << (24 - 8 * idx))),
                        QuantumCell::Existing(&sum),
                    );
                }
                gate.assert_equal(
                    ctx,
                    QuantumCell::Existing(&assigned_word),
                    QuantumCell::Existing(&sum),
                );
                assigned_bytes
            })
            .collect::<Vec<AssignedValue<F>>>();
        let result = AssignedHashResult {
            input_len: assigned_input_byte_size,
            input_bytes: assigned_input_bytes,
            output_bytes: output_digest_bytes,
        };
        self.cur_hash_idx += 1;
        Ok(result)
    }

    pub fn new_context<'a, 'b>(&'b self, region: Region<'a, F>) -> Context<'a, F> {
        Context::new(
            region,
            ContextParams {
                max_rows: self.range.gate.max_rows,
                num_context_ids: 1,
                fixed_columns: self.range.gate.constants.clone(),
            },
        )
    }

    pub fn range(&self) -> &RangeConfig<F> {
        &self.range
    }

    pub fn load(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        self.spread_config.load(layouter)
    }
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use super::*;
    use halo2_base::halo2_proofs::{
        circuit::{Cell, Layouter, Region, SimpleFloorPlanner},
        dev::MockProver,
        halo2curves::bn256::Fr,
        plonk::{Circuit, ConstraintSystem, Instance},
    };
    use halo2_base::{gates::range::RangeStrategy::Vertical, ContextParams, SKIP_FIRST_PASS};

    use num_bigint::RandomBits;
    use rand::rngs::OsRng;
    use rand::{thread_rng, Rng};

    #[derive(Debug, Clone)]
    struct TestConfig<F: PrimeField> {
        sha256: Sha256DynamicConfig<F>,
        hash_column: Column<Instance>,
    }

    #[derive(Debug, Clone)]
    struct TestCircuit<F: PrimeField> {
        test_inputs: Vec<Vec<u8>>,
        precomputed_input_lens: Vec<usize>,
        _f: PhantomData<F>,
    }

    impl<F: PrimeField> Circuit<F> for TestCircuit<F> {
        type Config = TestConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let range_config = RangeConfig::configure(
                meta,
                Vertical,
                &[Self::NUM_ADVICE],
                &[Self::NUM_LOOKUP_ADVICE],
                Self::NUM_FIXED,
                Self::LOOKUP_BITS,
                0,
                17,
            );
            let hash_column = meta.instance_column();
            meta.enable_equality(hash_column);
            let sha256: Sha256DynamicConfig<F> = Sha256DynamicConfig::configure(
                meta,
                vec![Self::MAX_BYTE_SIZE1, Self::MAX_BYTE_SIZE2],
                range_config,
                8,
                2,
                true,
            );
            Self::Config {
                sha256,
                hash_column,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let mut sha256 = config.sha256.clone();
            let range = sha256.range().clone();
            sha256.range().load_lookup_table(&mut layouter)?;
            sha256.load(&mut layouter)?;
            let mut first_pass = SKIP_FIRST_PASS;
            let mut assigned_hash_cells = vec![];
            layouter.assign_region(
                || "dynamic sha2 test",
                |region| {
                    if first_pass {
                        first_pass = false;
                        return Ok(());
                    }

                    let ctx = &mut sha256.new_context(region);
                    let result0 = sha256.digest(
                        ctx,
                        &self.test_inputs[0],
                        Some(self.precomputed_input_lens[0]),
                    )?;
                    assigned_hash_cells
                        .append(&mut result0.output_bytes.into_iter().map(|v| v.cell()).collect());
                    let result1 = sha256.digest(
                        ctx,
                        &self.test_inputs[1],
                        Some(self.precomputed_input_lens[1]),
                    )?;
                    assigned_hash_cells
                        .append(&mut result1.output_bytes.into_iter().map(|v| v.cell()).collect());
                    range.finalize(ctx);
                    {
                        println!("total advice cells: {}", ctx.total_advice);
                        let const_rows = ctx.total_fixed + 1;
                        println!("maximum rows used by a fixed column: {const_rows}");
                        println!("lookup cells used: {}", ctx.cells_to_lookup.len());
                    }
                    Ok(())
                },
            )?;
            for (idx, hash) in assigned_hash_cells.into_iter().enumerate() {
                layouter.constrain_instance(hash, config.hash_column, idx)?;
            }
            Ok(())
        }
    }

    impl<F: PrimeField> TestCircuit<F> {
        const MAX_BYTE_SIZE1: usize = 128;
        const MAX_BYTE_SIZE2: usize = 128;
        const NUM_ADVICE: usize = 3;
        const NUM_FIXED: usize = 1;
        const NUM_LOOKUP_ADVICE: usize = 1;
        const LOOKUP_BITS: usize = 16;
    }

    #[test]
    fn test_sha256_correct1() {
        let k = 17;

        // Test vector: "abc"
        let test_input = vec!['a' as u8, 'b' as u8, 'c' as u8];

        let circuit = TestCircuit::<Fr> {
            test_inputs: vec![test_input, vec![]],
            precomputed_input_lens: vec![0, 0],
            _f: PhantomData,
        };
        let test_output0: [u8; 32] = [
            0b10111010, 0b01111000, 0b00010110, 0b10111111, 0b10001111, 0b00000001, 0b11001111,
            0b11101010, 0b01000001, 0b01000001, 0b01000000, 0b11011110, 0b01011101, 0b10101110,
            0b00100010, 0b00100011, 0b10110000, 0b00000011, 0b01100001, 0b10100011, 0b10010110,
            0b00010111, 0b01111010, 0b10011100, 0b10110100, 0b00010000, 0b11111111, 0b01100001,
            0b11110010, 0b00000000, 0b00010101, 0b10101101,
        ];
        let test_output1 =
            hex::decode("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
                .unwrap();
        let test_output = vec![test_output0.to_vec(), test_output1]
            .concat()
            .into_iter()
            .map(|val| Fr::from_u128(val as u128))
            .collect();
        let public_inputs = vec![test_output];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_sha256_correct2() {
        let k = 17;

        // Test vector: "0x0"
        let test_input = vec![0u8];

        let circuit = TestCircuit::<Fr> {
            test_inputs: vec![test_input, vec![]],
            precomputed_input_lens: vec![0, 0],
            _f: PhantomData,
        };
        let test_output0 =
            hex::decode("6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d")
                .unwrap();
        let test_output1 =
            hex::decode("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
                .unwrap();
        let test_output = vec![test_output0, test_output1]
            .concat()
            .into_iter()
            .map(|val| Fr::from_u128(val as u128))
            .collect();
        let public_inputs = vec![test_output];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_sha256_correct3() {
        let k = 17;

        let test_inputs = vec![vec![0x1; 56], vec![0u8, 0u8, 0u8]];

        let circuit = TestCircuit::<Fr> {
            test_inputs,
            precomputed_input_lens: vec![0, 0],
            _f: PhantomData,
        };
        let test_output0 =
            hex::decode("51e14a913680f24c85fe3b0e2e5b57f7202f117bb214f8ffdd4ea0f4e921fd52")
                .unwrap();
        let test_output1 =
            hex::decode("709e80c88487a2411e1ee4dfb9f22a861492d20c4765150c0c794abd70f8147c")
                .unwrap();
        let test_output = vec![test_output0, test_output1]
            .concat()
            .into_iter()
            .map(|val| Fr::from_u128(val as u128))
            .collect();
        let public_inputs = vec![test_output];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }

    #[test]
    fn test_sha256_correct4() {
        let k = 17;

        fn gen_random_bytes(len: usize) -> Vec<u8> {
            let mut rng = thread_rng();
            (0..len).map(|_| rng.gen::<u8>()).collect()
        }
        let test_inputs = vec![gen_random_bytes(128 + 64), gen_random_bytes(128 + 64)];
        let test_output0 = Sha256::digest(&test_inputs[0]);
        let test_output1 = Sha256::digest(&test_inputs[1]);
        let circuit = TestCircuit::<Fr> {
            test_inputs,
            precomputed_input_lens: vec![128, 128],
            _f: PhantomData,
        };
        let test_output = vec![test_output0, test_output1]
            .concat()
            .into_iter()
            .map(|val| Fr::from_u128(val as u128))
            .collect();
        let public_inputs = vec![test_output];

        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
