// //! Gadget and chips for the [SHA-256] hash function.
// //!
// //! [SHA-256]: https://tools.ietf.org/html/rfc6234
use eth_types::Field;
use halo2_base::halo2_proofs::{
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner, Value},
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
use sha2::{Digest, Sha256};
use zkevm_circuits::sha256_circuit::sha256_bit::{Sha256BitChip, Sha256BitConfig};

const Sha256BitChipRowPerRound: usize = 72;
const BLOCK_BYTE: usize = 64;
const DIGEST_BYTE: usize = 32;
#[derive(Debug, Clone)]
pub struct Sha256DynamicConfig<F: Field> {
    sha256_bit_config: Sha256BitConfig<F>,
    max_byte_size: usize,
    range: RangeConfig<F>,
    //range_config: RangeConfig,
    // pub bytes: Column<Advice>,
    // pub table_bytes: TableColumn,
    // pub sel_bytes: Selector,
}

impl<F: Field> Sha256DynamicConfig<F> {
    pub fn construct(
        sha256_bit_config: Sha256BitConfig<F>,
        max_byte_size: usize,
        range: RangeConfig<F>,
    ) -> Self {
        Self {
            sha256_bit_config,
            max_byte_size,
            range,
        }
    }

    pub fn digest<'a, 'b: 'a>(
        &'a self,
        //mut layouter: impl Layouter<F>,
        ctx: &mut Context<'b, F>,
        input: &'a [u8],
    ) -> Result<
        (
            AssignedValue<'b, F>,
            Vec<AssignedValue<'b, F>>,
            Vec<AssignedValue<'b, F>>,
        ),
        Error,
    > {
        let input_byte_size = input.len();
        let max_byte_size = self.max_byte_size;
        assert!(input_byte_size <= max_byte_size);
        let range = &self.range;
        let gate = &range.gate;
        let sha256_bit_chip = Sha256BitChip::new(self.sha256_bit_config.clone(), max_byte_size);
        let assigned_rows = sha256_bit_chip.digest(&mut ctx.region, input)?;
        // let assigned_rows = layouter.assign_region(
        //     || "assigned_rows",
        //     |mut region| sha256_bit_chip.digest(&mut region, input),
        // )?;

        let input_byte_size_with_9 = input_byte_size + 9;
        let one_round_size = BLOCK_BYTE;
        let num_round = if input_byte_size_with_9 % one_round_size == 0 {
            input_byte_size_with_9 / one_round_size
        } else {
            input_byte_size_with_9 / one_round_size + 1
        };
        let padded_size = one_round_size * num_round;
        let zero_padding_byte_size = padded_size - input_byte_size - 9;
        let max_round = max_byte_size / one_round_size;
        let remaining_byte_size = max_byte_size - padded_size;
        assert_eq!(
            remaining_byte_size,
            one_round_size * (max_round - num_round)
        );

        let mut assigned_input = vec![];
        let mut assign_byte = |byte: u8| gate.load_witness(ctx, Value::known(F::from(byte as u64)));
        for byte in input.iter() {
            //range.range_check(ctx, &assigned, 8);
            assigned_input.push(assign_byte(*byte));
        }
        assigned_input.push(assign_byte(0x80));
        for _ in 0..zero_padding_byte_size {
            assigned_input.push(assign_byte(0u8));
        }
        let mut input_len_bytes = [0; 8];
        let le_size_bytes = (8 * input_byte_size).to_le_bytes();
        input_len_bytes[0..le_size_bytes.len()].copy_from_slice(&le_size_bytes);
        for byte in input_len_bytes.iter().rev() {
            assigned_input.push(assign_byte(*byte));
        }
        assert_eq!(assigned_input.len(), num_round * one_round_size);
        for _ in 0..remaining_byte_size {
            assigned_input.push(assign_byte(0u8));
        }
        assert_eq!(assigned_input.len(), max_byte_size);
        for assigned in assigned_input.iter() {
            range.range_check(ctx, assigned, 8);
        }

        let zero = gate.load_zero(ctx);
        let mut sum_input_len = zero.clone();
        let mut sum_hash_bytes = vec![zero.clone(); 32];
        for round_idx in 0..max_round {
            let input_len = self.assigned_cell2value(ctx, &assigned_rows.input_len[round_idx])?;
            let input_words = assigned_rows.input_words[16 * round_idx..16 * (round_idx + 1)]
                .into_iter()
                .map(|v| self.assigned_cell2value(ctx, v))
                .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
            let is_output_enabled =
                self.assigned_cell2value(ctx, &assigned_rows.is_output_enabled[round_idx])?;
            let output_words = assigned_rows.output_words[4 * round_idx..4 * round_idx + 4]
                .into_iter()
                .map(|v| self.assigned_cell2value(ctx, v))
                .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
            //let is_dummy = &assigned_rows.is_dummy[round_idx];

            sum_input_len = {
                let muled = gate.mul(
                    ctx,
                    QuantumCell::Existing(&is_output_enabled),
                    QuantumCell::Existing(&input_len),
                );
                gate.add(
                    ctx,
                    QuantumCell::Existing(&sum_input_len),
                    QuantumCell::Existing(&muled),
                )
            };

            for word_idx in 0..16 {
                let offset_in = 64 * round_idx + 4 * word_idx;
                let assigned_input_u32 = &assigned_input[offset_in + 0..offset_in + 4];
                let mut sum = zero.clone();
                for (idx, assigned_byte) in assigned_input_u32.iter().enumerate() {
                    sum = gate.mul_add(
                        ctx,
                        QuantumCell::Existing(assigned_byte),
                        QuantumCell::Constant(F::from_u128(1u128 << (8 * idx))),
                        QuantumCell::Existing(&sum),
                    );
                }
                gate.assert_equal(
                    ctx,
                    QuantumCell::Existing(&sum),
                    QuantumCell::Existing(&input_words[word_idx]),
                );
            }

            for word_idx in 0..4 {
                let hash_bytes_val = (0..8)
                    .map(|idx| {
                        output_words[word_idx]
                            .value()
                            .map(|v| (v.get_lower_128() >> (8 * idx)) & ((1u128 << 8) - 1u128))
                            .map(|v| F::from_u128(v))
                    })
                    .collect::<Vec<Value<F>>>();
                let assigned_hash_bytes = hash_bytes_val
                    .iter()
                    .map(|v| gate.load_witness(ctx, *v))
                    .collect::<Vec<AssignedValue<F>>>();
                let mut sum = zero.clone();
                for (idx, assigned_byte) in assigned_hash_bytes.iter().enumerate() {
                    sum = gate.mul_add(
                        ctx,
                        QuantumCell::Existing(&assigned_byte),
                        QuantumCell::Constant(F::from(1 << (8 * idx))),
                        QuantumCell::Existing(&sum),
                    );
                }
                gate.assert_equal(
                    ctx,
                    QuantumCell::Existing(&sum),
                    QuantumCell::Existing(&output_words[word_idx]),
                );
                for idx in 0..8 {
                    sum_hash_bytes[8 * word_idx + idx] = gate.mul_add(
                        ctx,
                        QuantumCell::Existing(&is_output_enabled),
                        QuantumCell::Existing(&assigned_hash_bytes[idx]),
                        QuantumCell::Existing(&sum_hash_bytes[8 * word_idx + idx]),
                    );
                }
            }
        }
        for byte in sum_hash_bytes.iter() {
            range.range_check(ctx, byte, 8);
        }

        Ok((sum_input_len, assigned_input, sum_hash_bytes))
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

    fn assigned_cell2value<'v>(
        &self,
        ctx: &mut Context<'v, F>,
        assigned_cell: &AssignedCell<F, F>,
    ) -> Result<AssignedValue<'v, F>, Error> {
        let gate = self.range.gate();
        let assigned_value = gate.load_witness(ctx, assigned_cell.value().map(|v| *v));
        ctx.region
            .constrain_equal(assigned_cell.cell(), assigned_value.cell())?;
        Ok(assigned_value)
    }
}

#[cfg(test)]
mod test {
    use std::marker::PhantomData;

    use super::*;
    use eth_types::Field;
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
    struct TestConfig<F: Field> {
        sha256: Sha256DynamicConfig<F>,
        hash_column: Column<Instance>,
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
            let sha256_bit_config = Sha256BitConfig::configure(meta);
            let range_config = RangeConfig::configure(
                meta,
                Vertical,
                &[Self::NUM_ADVICE],
                &[Self::NUM_LOOKUP_ADVICE],
                Self::NUM_FIXED,
                Self::LOOKUP_BITS,
                0,
                13,
            );
            let hash_column = meta.instance_column();
            meta.enable_equality(hash_column);
            let sha256 = Sha256DynamicConfig::construct(
                sha256_bit_config,
                Self::MAX_BYTE_SIZE,
                range_config,
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
            let sha256 = config.sha256.clone();
            let range = sha256.range.clone();
            sha256.range.load_lookup_table(&mut layouter)?;
            let mut first_pass = SKIP_FIRST_PASS;
            let assigned_hash_cells = layouter.assign_region(
                || "random rsa modpow test with 2048 bits public keys",
                |region| {
                    if first_pass {
                        first_pass = false;
                        return Ok(vec![]);
                    }

                    let ctx = &mut sha256.new_context(region);
                    let (_, _, assigned_hash) = sha256.digest(ctx, &self.test_input)?;
                    range.finalize(ctx);
                    {
                        println!("total advice cells: {}", ctx.total_advice);
                        let const_rows = ctx.total_fixed + 1;
                        println!("maximum rows used by a fixed column: {const_rows}");
                        println!("lookup cells used: {}", ctx.cells_to_lookup.len());
                    }
                    Ok(assigned_hash.into_iter().map(|v| v.cell()).collect())
                },
            )?;
            for (idx, hash) in assigned_hash_cells.into_iter().enumerate() {
                layouter.constrain_instance(hash, config.hash_column, idx)?;
            }
            Ok(())
        }
    }

    impl<F: Field> TestCircuit<F> {
        const MAX_BYTE_SIZE: usize = 1024;
        const NUM_ADVICE: usize = 50;
        const NUM_FIXED: usize = 1;
        const NUM_LOOKUP_ADVICE: usize = 4;
        const LOOKUP_BITS: usize = 12;
    }

    #[test]
    fn test_sha256_correct1() {
        let k = 13;

        // Test vector: "abc"
        let test_input = vec!['a' as u8, 'b' as u8, 'c' as u8];

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
        let k = 13;

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
        let k = 13;

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
