mod circuit;
mod compression;
mod gate;
pub(crate) mod spread;
pub(crate) mod utils;
use std::convert::TryInto;

pub use compression::*;

use gate::ShaThreadBuilder;
use halo2_base::halo2_proofs::plonk::Error;
use halo2_base::safe_types::{RangeChip, RangeInstructions};
use halo2_base::utils::ScalarField;
use halo2_base::QuantumCell;
use halo2_base::{gates::GateInstructions, AssignedValue};
use itertools::Itertools;
use spread::{SpreadChip, SpreadConfig};

// const Sha256BitChipRowPerRound: usize = 72;
const BLOCK_SIZE: usize = 64;
// const DIGEST_SIZE: usize = 32;

#[derive(Debug, Clone)]
pub struct AssignedHashResult<F: ScalarField> {
    pub input_len: AssignedValue<F>,
    pub input_bytes: Vec<AssignedValue<F>>,
    pub output_bytes: [AssignedValue<F>; 32],
}

pub struct Sha256Chip<'a, F: ScalarField> {
    spread: SpreadChip<'a, F>,
}

impl<'a, F: ScalarField> Sha256Chip<'a, F> {
    pub fn new(range: &'a RangeChip<F>) -> Self {
        Self {
            spread: SpreadChip::new(range),
        }
    }

    pub fn digest<const MAX_INPUT_SIZE: usize>(
        &self,
        thread_pool: &mut ShaThreadBuilder<F>,
        input: &'a [u8],
        strict: bool,
    ) -> Result<AssignedHashResult<F>, Error> {
        let assigned_input = input
            .iter()
            .map(|byte| thread_pool.main().load_witness(F::from(*byte as u64)))
            .collect_vec();

        self.digest_assigned::<MAX_INPUT_SIZE>(thread_pool, assigned_input, strict)
    }

    pub fn digest_assigned<const MAX_INPUT_SIZE: usize>(
        &self,
        thread_pool: &mut ShaThreadBuilder<F>,
        assigned_input: Vec<AssignedValue<F>>,
        strict: bool,
    ) -> Result<AssignedHashResult<F>, Error> {
        let max_processed_bytes = {
            let mut max_bytes = MAX_INPUT_SIZE + 9;
            let remainder = max_bytes % 64;
            if remainder != 0 {
                max_bytes += 64 - remainder;
            }
            max_bytes
        };

        let mut assigned_input_bytes = assigned_input.to_vec();
        let input_byte_size = assigned_input_bytes.len();
        let input_byte_size_with_9 = input_byte_size + 9;
        assert!(input_byte_size <= MAX_INPUT_SIZE);
        let range = self.spread.range();
        let gate = &range.gate;

        let one_round_size = BLOCK_SIZE;

        let num_round = if input_byte_size_with_9 % one_round_size == 0 {
            input_byte_size_with_9 / one_round_size
        } else {
            input_byte_size_with_9 / one_round_size + 1
        };
        let max_round = max_processed_bytes / one_round_size;
        let padded_size = one_round_size * num_round;
        let zero_padding_byte_size = padded_size - input_byte_size_with_9;
        // let remaining_byte_size = MAX_INPUT_SIZE - padded_size;
        // assert_eq!(
        //     remaining_byte_size,
        //     one_round_size * (max_round - num_round)
        // );
        let mut assign_byte = |byte: u8| thread_pool.main().load_witness(F::from(byte as u64));

        assigned_input_bytes.push(assign_byte(0x80));

        for _ in 0..zero_padding_byte_size {
            assigned_input_bytes.push(assign_byte(0u8));
        }

        let mut input_len_bytes = [0; 8];
        let le_size_bytes = (8 * input_byte_size).to_le_bytes();
        input_len_bytes[0..le_size_bytes.len()].copy_from_slice(&le_size_bytes);
        for byte in input_len_bytes.iter().rev() {
            assigned_input_bytes.push(assign_byte(*byte));
        }

        assert_eq!(assigned_input_bytes.len(), num_round * one_round_size);
        // for _ in 0..remaining_byte_size {
        //     assigned_input_bytes.push(assign_byte(0u8));
        // }

        if strict {
            for &assigned in assigned_input_bytes.iter() {
                range.range_check(thread_pool.main(), assigned, 8);
            }
        }

        let assigned_num_round = thread_pool.main().load_witness(F::from(num_round as u64));

        // compute an initial state from the precomputed_input.
        let mut last_state = INIT_STATE;

        let mut assigned_last_state_vec = vec![last_state
            .iter()
            .map(|state| thread_pool.main().load_witness(F::from(*state as u64)))
            .collect_vec()];

        let mut num_processed_input = 0;
        while num_processed_input < max_processed_bytes {
            let assigned_input_word_at_round =
                &assigned_input_bytes[num_processed_input..(num_processed_input + one_round_size)];
            let new_assigned_hs_out = sha256_compression(
                thread_pool,
                &self.spread,
                assigned_input_word_at_round,
                assigned_last_state_vec.last().unwrap(),
            )?;

            assigned_last_state_vec.push(new_assigned_hs_out);
            num_processed_input += one_round_size;
        }

        let zero = thread_pool.main().load_zero();
        let mut output_h_out = vec![zero; 8];
        for (n_round, assigned_state) in assigned_last_state_vec.into_iter().enumerate() {
            let selector = gate.is_equal(
                thread_pool.main(),
                QuantumCell::Constant(F::from(n_round as u64)),
                assigned_num_round,
            );
            for i in 0..8 {
                output_h_out[i] = gate.select(
                    thread_pool.main(),
                    assigned_state[i],
                    output_h_out[i],
                    selector,
                )
            }
        }
        let output_digest_bytes = output_h_out
            .into_iter()
            .flat_map(|assigned_word| {
                let be_bytes = assigned_word.value().get_lower_32().to_be_bytes().to_vec();
                let assigned_bytes = (0..4)
                    .map(|idx| {
                        let assigned = thread_pool
                            .main()
                            .load_witness(F::from(be_bytes[idx] as u64));
                        range.range_check(thread_pool.main(), assigned, 8);
                        assigned
                    })
                    .collect_vec();
                let mut sum = thread_pool.main().load_zero();
                for (idx, assigned_byte) in assigned_bytes.iter().copied().enumerate() {
                    sum = gate.mul_add(
                        thread_pool.main(),
                        assigned_byte,
                        QuantumCell::Constant(F::from(1u64 << (24 - 8 * idx))),
                        sum,
                    );
                }
                thread_pool.main().constrain_equal(&assigned_word, &sum);
                assigned_bytes
            })
            .collect_vec()
            .try_into()
            .unwrap();

        let result = AssignedHashResult {
            input_bytes: assigned_input_bytes,
            output_bytes: output_digest_bytes,
            input_len: todo!(),
        };
        Ok(result)
    }

    fn range(&self) -> &RangeChip<F> {
        self.spread.range()
    }
}

// #[cfg(test)]
// mod test {
//     use std::marker::PhantomData;

//     use super::*;
//     use halo2_base::halo2_proofs::{
//         circuit::{Cell, Layouter, Region, SimpleFloorPlanner},
//         dev::MockProver,
//         halo2curves::bn256::Fr,
//         plonk::{Circuit, ConstraintSystem, Instance},
//     };
//     use halo2_base::{gates::range::RangeStrategy::Vertical, ContextParams, SKIP_FIRST_PASS};

//     use num_bigint::RandomBits;
//     use rand::rngs::OsRng;
//     use rand::{thread_rng, Rng};

//     #[derive(Debug, Clone)]
//     struct TestConfig<F: PrimeField> {
//         sha256: Sha256DynamicConfig<F>,
//         hash_column: Column<Instance>,
//     }

//     #[derive(Debug, Clone)]
//     struct TestCircuit<F: PrimeField> {
//         test_inputs: Vec<Vec<u8>>,
//         precomputed_input_lens: Vec<usize>,
//         _f: PhantomData<F>,
//     }

//     impl<F: PrimeField> Circuit<F> for TestCircuit<F> {
//         type Config = TestConfig<F>;
//         type FloorPlanner = SimpleFloorPlanner;

//         fn without_witnesses(&self) -> Self {
//             unimplemented!()
//         }

//         fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
//             let range_config = RangeConfig::configure(
//                 meta,
//                 Vertical,
//                 &[Self::NUM_ADVICE],
//                 &[Self::NUM_LOOKUP_ADVICE],
//                 Self::NUM_FIXED,
//                 Self::LOOKUP_BITS,
//                 0,
//                 17,
//             );
//             let hash_column = meta.instance_column();
//             meta.enable_equality(hash_column);
//             let sha256: Sha256DynamicConfig<F> = Sha256DynamicConfig::configure(
//                 meta,
//                 vec![Self::MAX_BYTE_SIZE1, Self::MAX_BYTE_SIZE2],
//                 range_config,
//                 8,
//                 2,
//                 true,
//             );
//             Self::Config {
//                 sha256,
//                 hash_column,
//             }
//         }

//         fn synthesize(
//             &self,
//             config: Self::Config,
//             mut layouter: impl Layouter<F>,
//         ) -> Result<(), Error> {
//             let mut sha256 = config.sha256.clone();
//             let range = sha256.range().clone();
//             sha256.range().load_lookup_table(&mut layouter)?;
//             sha256.load(&mut layouter)?;
//             let mut first_pass = SKIP_FIRST_PASS;
//             let mut assigned_hash_cells = vec![];
//             layouter.assign_region(
//                 || "dynamic sha2 test",
//                 |region| {
//                     if first_pass {
//                         first_pass = false;
//                         return Ok(());
//                     }

//                     let ctx = &mut sha256.new_context(region);
//                     let result0 = sha256.digest(
//                         ctx,
//                         &self.test_inputs[0],
//                         Some(self.precomputed_input_lens[0]),
//                     )?;
//                     assigned_hash_cells
//                         .append(&mut result0.output_bytes.into_iter().map(|v| v.cell()).collect());
//                     let result1 = sha256.digest(
//                         ctx,
//                         &self.test_inputs[1],
//                         Some(self.precomputed_input_lens[1]),
//                     )?;
//                     assigned_hash_cells
//                         .append(&mut result1.output_bytes.into_iter().map(|v| v.cell()).collect());
//                     range.finalize(ctx);
//                     {
//                         println!("total advice cells: {}", ctx.total_advice);
//                         let const_rows = ctx.total_fixed + 1;
//                         println!("maximum rows used by a fixed column: {const_rows}");
//                         println!("lookup cells used: {}", ctx.cells_to_lookup.len());
//                     }
//                     Ok(())
//                 },
//             )?;
//             for (idx, hash) in assigned_hash_cells.into_iter().enumerate() {
//                 layouter.constrain_instance(hash, config.hash_column, idx)?;
//             }
//             Ok(())
//         }
//     }

//     impl<F: PrimeField> TestCircuit<F> {
//         const MAX_BYTE_SIZE1: usize = 128;
//         const MAX_BYTE_SIZE2: usize = 128;
//         const NUM_ADVICE: usize = 3;
//         const NUM_FIXED: usize = 1;
//         const NUM_LOOKUP_ADVICE: usize = 1;
//         const LOOKUP_BITS: usize = 16;
//     }

//     #[test]
//     fn test_sha256_correct1() {
//         let k = 17;

//         // Test vector: "abc"
//         let test_input = vec!['a' as u8, 'b' as u8, 'c' as u8];

//         let circuit = TestCircuit::<Fr> {
//             test_inputs: vec![test_input, vec![]],
//             precomputed_input_lens: vec![0, 0],
//             _f: PhantomData,
//         };
//         let test_output0: [u8; 32] = [
//             0b10111010, 0b01111000, 0b00010110, 0b10111111, 0b10001111, 0b00000001, 0b11001111,
//             0b11101010, 0b01000001, 0b01000001, 0b01000000, 0b11011110, 0b01011101, 0b10101110,
//             0b00100010, 0b00100011, 0b10110000, 0b00000011, 0b01100001, 0b10100011, 0b10010110,
//             0b00010111, 0b01111010, 0b10011100, 0b10110100, 0b00010000, 0b11111111, 0b01100001,
//             0b11110010, 0b00000000, 0b00010101, 0b10101101,
//         ];
//         let test_output1 =
//             hex::decode("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
//                 .unwrap();
//         let test_output = vec![test_output0.to_vec(), test_output1]
//             .concat()
//             .into_iter()
//             .map(|val| Fr::from_u128(val as u128))
//             .collect();
//         let public_inputs = vec![test_output];

//         let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
//         assert_eq!(prover.verify(), Ok(()));
//     }

//     #[test]
//     fn test_sha256_correct2() {
//         let k = 17;

//         // Test vector: "0x0"
//         let test_input = vec![0u8];

//         let circuit = TestCircuit::<Fr> {
//             test_inputs: vec![test_input, vec![]],
//             precomputed_input_lens: vec![0, 0],
//             _f: PhantomData,
//         };
//         let test_output0 =
//             hex::decode("6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d")
//                 .unwrap();
//         let test_output1 =
//             hex::decode("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
//                 .unwrap();
//         let test_output = vec![test_output0, test_output1]
//             .concat()
//             .into_iter()
//             .map(|val| Fr::from_u128(val as u128))
//             .collect();
//         let public_inputs = vec![test_output];

//         let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
//         assert_eq!(prover.verify(), Ok(()));
//     }

//     #[test]
//     fn test_sha256_correct3() {
//         let k = 17;

//         let test_inputs = vec![vec![0x1; 56], vec![0u8, 0u8, 0u8]];

//         let circuit = TestCircuit::<Fr> {
//             test_inputs,
//             precomputed_input_lens: vec![0, 0],
//             _f: PhantomData,
//         };
//         let test_output0 =
//             hex::decode("51e14a913680f24c85fe3b0e2e5b57f7202f117bb214f8ffdd4ea0f4e921fd52")
//                 .unwrap();
//         let test_output1 =
//             hex::decode("709e80c88487a2411e1ee4dfb9f22a861492d20c4765150c0c794abd70f8147c")
//                 .unwrap();
//         let test_output = vec![test_output0, test_output1]
//             .concat()
//             .into_iter()
//             .map(|val| Fr::from_u128(val as u128))
//             .collect();
//         let public_inputs = vec![test_output];

//         let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
//         assert_eq!(prover.verify(), Ok(()));
//     }

//     #[test]
//     fn test_sha256_correct4() {
//         let k = 17;

//         fn gen_random_bytes(len: usize) -> Vec<u8> {
//             let mut rng = thread_rng();
//             (0..len).map(|_| rng.gen::<u8>()).collect()
//         }
//         let test_inputs = vec![gen_random_bytes(128 + 64), gen_random_bytes(128 + 64)];
//         let test_output0 = Sha256::digest(&test_inputs[0]);
//         let test_output1 = Sha256::digest(&test_inputs[1]);
//         let circuit = TestCircuit::<Fr> {
//             test_inputs,
//             precomputed_input_lens: vec![128, 128],
//             _f: PhantomData,
//         };
//         let test_output = vec![test_output0, test_output1]
//             .concat()
//             .into_iter()
//             .map(|val| Fr::from_u128(val as u128))
//             .collect();
//         let public_inputs = vec![test_output];

//         let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
//         assert_eq!(prover.verify(), Ok(()));
//     }
// }
