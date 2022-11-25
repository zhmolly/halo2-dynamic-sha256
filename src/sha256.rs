//! Gadget and chips for the [SHA-256] hash function.
//!
//! [SHA-256]: https://tools.ietf.org/html/rfc6234

use std::convert::TryInto;
use std::fmt;
use std::{cmp::min, ops::Deref};

use crate::{
    AssignedBits, BlockWord, RoundWordDense, State, Table16Chip, Table16Config, BLOCK_SIZE,
    DIGEST_SIZE, STATE,
};
use halo2wrong::{
    halo2::{
        arithmetic::FieldExt,
        circuit::{layouter, AssignedCell, Chip, Layouter, Value},
        plonk::{Advice, Column, ConstraintSystem, Error, Selector},
    },
    RegionCtx,
};

// use crate::{BlockWord, Table16Chip, Table16Config};

pub trait Sha256Compression<F: FieldExt>: Chip<F> {
    /// Variable representing the SHA-256 internal state.
    type State: Clone + fmt::Debug;
    /// Variable representing a 32-bit word of the input block to the SHA-256 compression
    /// function.
    type BlockWord: Copy + fmt::Debug + Default + From<u32>;

    /// Places the SHA-256 IV in the circuit, returning the initial state variable.
    fn initialization_vector(&self, layouter: &mut impl Layouter<F>) -> Result<Self::State, Error>;

    /// Creates an initial state from the output state of a previous block
    fn initialization(
        &self,
        layouter: &mut impl Layouter<F>,
        init_state: &Self::State,
    ) -> Result<Self::State, Error>;

    /// Starting from the given initialized state, processes a block of input and returns the
    fn compress(
        &self,
        layouter: &mut impl Layouter<F>,
        initialized_state: &Self::State,
        input: [BlockWord; super::BLOCK_SIZE],
    ) -> Result<(Self::State, Vec<AssignedBits<32, F>>), Error>;

    /*
    /// Converts the given state into a message digest.
    fn digest(
        &self,
        layouter: &mut impl Layouter<F>,
        state: &Self::State,
    ) -> Result<[Self::BlockWord; DIGEST_SIZE], Error>;*/
}

/*
/// The output of a SHA-256 circuit invocation.
#[derive(Debug)]
pub struct Sha256Digest<BlockWord>(pub [BlockWord; DIGEST_SIZE]);*/

use maingate::{
    AssignedValue, MainGate, MainGateConfig, MainGateInstructions, RangeChip, RangeConfig,
    RangeInstructions,
};

#[derive(Debug, Clone)]
pub struct Sha256Config {
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
    table16_config: Table16Config,
    max_byte_size: usize,
    max_round: usize,
    /*is_real_input: Column<Advice>,
    real_input_byte_acc: Column<Advice>,
    is_zero_padding: Column<Advice>,
    zero_padding_byte_acc: Column<Advice>,
    is_len_padding: Column<Advice>,
    len_padding_byte_acc: Column<Advice>,*/
}

pub type AssignedDigest<F> = [AssignedValue<F>; DIGEST_SIZE];

/// A gadget that constrains a SHA-256 invocation. It supports input at a granularity of
/// 32 bits.
#[derive(Debug)]
pub struct Sha256Chip<F: FieldExt> {
    config: Sha256Config,
    states: Vec<State<F>>,
}

impl<F: FieldExt> Sha256Chip<F> {
    const NUM_LOOKUP_TABLES: usize = 8;
    /// Create a new hasher instance.
    pub fn new(config: Sha256Config) -> Self {
        let states = Vec::new();
        Self { config, states }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>, max_byte_size: usize) -> Sha256Config {
        let main_gate_config = MainGate::configure(meta);
        let composition_bit_lens = vec![8 / Self::NUM_LOOKUP_TABLES, 32 / Self::NUM_LOOKUP_TABLES];
        let range_config =
            RangeChip::configure(meta, &main_gate_config, composition_bit_lens, vec![]);
        let table16_config = Table16Chip::configure(meta);

        let one_round_size = 4 * BLOCK_SIZE;
        let max_round = if max_byte_size % one_round_size == 0 {
            max_byte_size / one_round_size
        } else {
            max_byte_size / one_round_size
        };

        /*let is_real_input = meta.advice_column();
        let real_input_byte_acc = meta.advice_column();
        let is_zero_padding = meta.advice_column();
        let zero_padding_byte_acc = meta.advice_column();
        let is_len_padding = meta.advice_column();
        let len_padding_byte_acc = meta.advice_column();
        for column in [
            is_real_input,
            real_input_byte_acc,
            is_zero_padding,
            zero_padding_byte_acc,
            is_len_padding,
            len_padding_byte_acc,
        ] {
            meta.enable_equality(column)
        }*/
        Sha256Config {
            main_gate_config,
            range_config,
            table16_config,
            max_byte_size,
            max_round,
            /*is_real_input,
            real_input_byte_acc,
            is_zero_padding,
            zero_padding_byte_acc,
            is_len_padding,
            len_padding_byte_acc,*/
        }
    }

    pub fn init(&mut self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let table16_chip = self.table16_chip();
        let init_state = table16_chip.initialization_vector(layouter)?;
        self.states.push(init_state);
        Ok(())
    }

    pub fn internal_assigned_digest(
        &self,
        ctx: &mut RegionCtx<F>,
        idx: usize,
    ) -> Result<AssignedDigest<F>, Error> {
        self.state_to_assigned_halves(ctx, &self.states[idx])
    }

    pub fn last_assigned_digest(&self, ctx: &mut RegionCtx<F>) -> Result<AssignedDigest<F>, Error> {
        self.internal_assigned_digest(ctx, self.states.len() - 1)
    }

    pub fn update(
        &mut self,
        ctx: &mut RegionCtx<F>,
        layouter: &mut impl Layouter<F>,
        inputs: &[Value<u8>],
    ) -> Result<(AssignedDigest<F>, Vec<AssignedValue<F>>), Error> {
        let input_byte_size = inputs.len();
        assert!(input_byte_size <= self.config.max_byte_size);
        let input_byte_size_with64 = input_byte_size + 8;
        let one_round_size = 4 * BLOCK_SIZE;
        let num_round = if input_byte_size_with64 % one_round_size == 0 {
            input_byte_size_with64 / one_round_size
        } else {
            input_byte_size_with64 / one_round_size
        };
        let padded_size = one_round_size * num_round;
        let zero_padding_byte_size = padded_size - input_byte_size - 8;
        let max_byte_size = self.config.max_byte_size;
        let max_round = self.config.max_round;
        let remaining_byte_size = max_byte_size - padded_size;

        let main_gate = self.main_gate();
        let assigned_inpu_byte_size =
            main_gate.assign_value(ctx, Value::known(F::from_u128(input_byte_size as u128)))?;
        let assigned_num_round =
            main_gate.assign_value(ctx, Value::known(F::from_u128(num_round as u128)))?;
        let assigned_one_round_size =
            main_gate.assign_constant(ctx, F::from_u128(one_round_size as u128))?;
        let assigned_max_byte_size =
            main_gate.assign_constant(ctx, F::from_u128(max_byte_size as u128))?;
        let assigned_max_round = main_gate.assign_constant(ctx, F::from_u128(max_round as u128))?;
        let eight = main_gate.assign_constant(ctx, F::from_u128(8u128))?;

        let assigned_padded_size =
            main_gate.mul(ctx, &assigned_one_round_size, &assigned_num_round)?;
        let assigned_zero_padding_byte_size = {
            let sub1 = main_gate.sub(ctx, &assigned_padded_size, &assigned_inpu_byte_size)?;
            main_gate.sub(ctx, &sub1, &eight)?;
        };
        let assigned_remaining_byte_size =
            main_gate.sub(ctx, &assigned_max_byte_size, &assigned_padded_size)?;
        /*let assigned_remaining_byte_size =
        main_gate.assign_value(ctx, Value::known(F::from_u128(remaining_byte_size as u128)))?;*/

        // 1. 0<= input_byte_size, num_round < 2^64
        let range_chip = self.range_chip();
        {
            let range_assigned = range_chip.assign(
                ctx,
                assigned_inpu_byte_size.value().map(|v| *v),
                64 / Self::NUM_LOOKUP_TABLES,
                64,
            )?;
            main_gate.assert_equal(ctx, &assigned_inpu_byte_size, &range_assigned)?;
        }
        {
            let range_assigned = range_chip.assign(
                ctx,
                assigned_num_round.value().map(|v| *v),
                64 / Self::NUM_LOOKUP_TABLES,
                64,
            )?;
            main_gate.assert_equal(ctx, &assigned_num_round, &range_assigned)?;
        }
        // 2. num_round <= max_round
        {
            let sub = main_gate.sub(ctx, &assigned_max_round, &assigned_num_round)?;
            let range_assigned = range_chip.assign(
                ctx,
                sub.value().map(|v| *v),
                64 / Self::NUM_LOOKUP_TABLES,
                64,
            )?;
            main_gate.assert_equal(ctx, &sub, &range_assigned)?;
        }
        // 3. Decompose input_byte_size into bytes.
        let input_size_decomposed_vals = input_byte_size
            .to_be_bytes()
            .iter()
            .map(|byte| F::from_u128(*byte as u128))
            .map(|val| range_chip.assign(ctx, Value::known(val), 8 / Self::NUM_LOOKUP_TABLES, 8))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        {
            let mut composed_val = main_gate.assign_constant(ctx, F::zero())?;
            let u1 = main_gate.assign_constant(ctx, F::from_u128(256u128))?;
            let mut coeff = main_gate.assign_constant(ctx, F::one())?;
            for val in input_size_decomposed_vals.iter().rev() {
                composed_val = main_gate.mul_add(ctx, val, &coeff, &composed_val)?;
                coeff = main_gate.mul(ctx, &coeff, &u1)?;
            }
            main_gate.assert_equal(ctx, &assigned_inpu_byte_size, &composed_val)?;
        }

        // 1. one_round_size * num_round == padded_size
        /*let round_mul = main_gate.mul(ctx, &assigned_one_round_size, &assigned_num_round)?;
        main_gate.assert_equal(ctx, &round_mul, &assigned_padded_size)?;
        // 2. padded_size == input_byte_size + padding_byte_size + 8(=input length byte)
        let byte_size_add = main_gate.add(
            ctx,
            &assigned_inpu_byte_size,
            &assigned_zero_padding_byte_size,
        )?;
        let byte_size_add = main_gate.add(ctx, &eight, &byte_size_add)?;
        main_gate.assert_equal(ctx, &byte_size_add, &assigned_padded_size)?;
        // 3. padded_size + remaining_byte_size == max_byte_size
        let byte_size_add =
            main_gate.add(ctx, &assigned_padded_size, &assigned_remaining_byte_size)?;
        main_gate.assert_equal(ctx, &byte_size_add, &assigned_max_byte_size)?;

        let range_chip = self.range_chip();
        // 3. 0<= input_bit_size < 2^64, 0<= num_round < 2^64,  <= max_bit_size
        let byte_size_sub =
            main_gate.sub(ctx, &assigned_max_byte_size, &assigned_inpu_byte_size)?;
        let range_assigned = range_chip.assign(
            ctx,
            byte_size_sub.value().map(|v| *v),
            64 / Self::NUM_LOOKUP_TABLES,
            64,
        )?;
        main_gate.assert_equal(ctx, &byte_size_sub, &range_assigned)?;
        // 4. num_round <= max_round
        let round_sub = main_gate.sub(ctx, &assigned_max_round, &assigned_num_round)?;
        let range_assigned = range_chip.assign(
            ctx,
            round_sub.value().map(|v| *v),
            64 / Self::NUM_LOOKUP_TABLES,
            64,
        )?;
        main_gate.assert_equal(ctx, &round_sub, &range_assigned)?;

        let input_size_decomposed_vals = input_byte_size
            .to_be_bytes()
            .iter()
            .map(|byte| F::from_u128(*byte as u128))
            .map(|val| range_chip.assign(ctx, Value::known(val), 8 / Self::NUM_LOOKUP_TABLES, 8))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        let mut composed_val = main_gate.assign_constant(ctx, F::zero())?;
        let u1 = main_gate.assign_constant(ctx, F::from_u128(256u128))?;
        let mut coeff = main_gate.assign_constant(ctx, F::one())?;
        for val in input_size_decomposed_vals.iter().rev() {
            composed_val = main_gate.mul_add(ctx, val, &coeff, &composed_val)?;
            coeff = main_gate.mul(ctx, &coeff, &u1)?;
        }
        main_gate.assert_equal(ctx, &assigned_inpu_byte_size, &composed_val)?;*/

        // 4. Construct real input bytes.
        let mut assigned_real_inputs = inputs
            .iter()
            .map(|val| {
                range_chip.assign(
                    ctx,
                    val.map(|v| F::from_u128(v as u128)),
                    8 / Self::NUM_LOOKUP_TABLES,
                    8,
                )
            })
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        for _ in 0..(max_byte_size - input_byte_size) {
            assigned_real_inputs.push(range_chip.assign(
                ctx,
                Value::known(F::zero()),
                8 / Self::NUM_LOOKUP_TABLES,
                8,
            )?);
        }

        // 5. Construct input_byte_len bytes.
        let mut assigned_len_padding_inputs = Vec::with_capacity(self.config.max_byte_size);
        for _ in 0..(input_byte_size + zero_padding_byte_size) {
            assigned_len_padding_inputs.push(range_chip.assign(
                ctx,
                Value::known(F::zero()),
                8 / Self::NUM_LOOKUP_TABLES,
                8,
            )?);
        }
        for i in 0..8 {
            assigned_len_padding_inputs.push(input_size_decomposed_vals[i].clone());
        }
        for _ in 0..remaining_byte_size {
            assigned_len_padding_inputs.push(range_chip.assign(
                ctx,
                Value::known(F::zero()),
                8 / Self::NUM_LOOKUP_TABLES,
                8,
            )?);
        }

        let is_real_input = (0..self.config.max_byte_size)
            .map(|i| {
                if i < input_byte_size {
                    main_gate.assign_bit(ctx, Value::known(F::one()))
                } else {
                    main_gate.assign_bit(ctx, Value::known(F::zero()))
                }
            })
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        let is_len_padding_input = (0..self.config.max_byte_size)
            .map(|i| {
                if (input_byte_size + zero_padding_byte_size) <= i
                    && i < (input_byte_size + zero_padding_byte_size + 8)
                {
                    main_gate.assign_bit(ctx, Value::known(F::one()))
                } else {
                    main_gate.assign_bit(ctx, Value::known(F::zero()))
                }
            })
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;

        let mut real_input_byte_acc = main_gate.assign_constant(ctx, F::zero())?;
        let mut real_eq_acc = main_gate.assign_constant(ctx, F::zero())?;
        main_gate.assert_one(ctx, &is_real_input[0])?;
        for i in 0..(max_byte_size - 1) {
            let is_next_eq = main_gate.is_equal(ctx, &is_real_input[i], &is_real_input[i + 1])?;
            let not_next_eq = main_gate.not(ctx, &is_next_eq)?;
            real_input_byte_acc = main_gate.add(ctx, &real_input_byte_acc, &is_real_input[i])?;
            let is_acc_eq =
                main_gate.is_equal(ctx, &real_input_byte_acc, &assigned_inpu_byte_size)?;
            real_eq_acc = main_gate.add(ctx, &real_eq_acc, &is_acc_eq)?;
            let is_vaild = main_gate.select(ctx, &not_next_eq, &is_next_eq, &is_acc_eq)?;
            main_gate.assert_one(ctx, &is_vaild)?;
        }
        main_gate.assert_one(ctx, &real_eq_acc)?;
        /*for i in 0..(self.config.max_byte_size - 1) {
            let is_next_eq = main_gate.is_equal(
                ctx,
                &is_zero_padding_input[i],
                &is_zero_padding_input[i + 1],
            )?;
            let not_next_eq = main_gate.not(ctx, &is_next_eq)?;
            zero_padding_byte_acc =
                main_gate.add(ctx, &zero_padding_byte_acc, &is_zero_padding_input[i])?;
            let is_acc_eq = main_gate.is_equal(
                ctx,
                &zero_padding_byte_acc,
                &assigned_zero_padding_byte_size,
            )?;
            let is_vaild = main_gate.select(ctx, &not_next_eq, &is_next_eq, &is_acc_eq)?;
            main_gate.assert_one(ctx, &is_vaild)?;
        }*/
        let mut len_padding_byte_acc = main_gate.assign_constant(ctx, F::zero())?;
        let mut len_eq_acc = main_gate.assign_constant(ctx, F::zero())?;
        main_gate.assert_zero(ctx, &is_len_padding_input[0])?;
        let before_len_padding_byte = main_gate.sub(ctx, &assigned_padded_size, &eight)?;
        let after_len_padding_byte = assigned_padded_size.clone();
        for i in 0..(max_byte_size - 1) {
            let is_next_eq =
                main_gate.is_equal(ctx, &is_len_padding_input[i], &is_len_padding_input[i + 1])?;
            let not_next_eq = main_gate.not(ctx, &is_next_eq)?;
            len_padding_byte_acc =
                main_gate.add(ctx, &len_padding_byte_acc, &is_len_padding_input[i])?;
            let is_acc_eq1 =
                main_gate.is_equal(ctx, &len_padding_byte_acc, &before_len_padding_byte)?;
            let is_acc_eq2 =
                main_gate.is_equal(ctx, &len_padding_byte_acc, &after_len_padding_byte)?;
            let eq_sum = main_gate.add(ctx, &is_acc_eq1, &is_acc_eq2)?;
            len_eq_acc = main_gate.add(ctx, &len_eq_acc, &eq_sum)?;
            let is_vaild = main_gate.select(ctx, &not_next_eq, &is_next_eq, &eq_sum)?;
            main_gate.assert_one(ctx, &is_vaild)?;
        }
        main_gate.assert_equal_to_constant(ctx, &len_eq_acc, F::from_u128(2))?;
        /*for i in 0..(self.config.max_byte_size - 1) {
            let is_real_turned_off =
                main_gate.sub(ctx, &is_real_input[i], &is_real_input[i + 1])?;
            let not_real_turned_off = main_gate.not(ctx, &is_real_turned_off)?;
            let is_zero_truned_on = main_gate.sub(
                ctx,
                &is_zero_padding_input[i + 1],
                &is_zero_padding_input[i],
            )?;
            let or1 = main_gate.or(ctx, &not_real_turned_off, &is_zero_truned_on)?;
            main_gate.assert_one(ctx, &or1)?;

            let is_zero_turned_off = main_gate.sub(
                ctx,
                &is_zero_padding_input[i],
                &is_zero_padding_input[i + 1],
            )?;
            let not_zero_turned_off = main_gate.not(ctx, &is_zero_turned_off)?;
            let is_len_truned_on =
                main_gate.sub(ctx, &is_len_padding_input[i + 1], &is_len_padding_input[i])?;
            let or2 = main_gate.or(ctx, &not_zero_turned_off, &is_len_truned_on)?;
            main_gate.assert_one(ctx, &or2)?;
        }*/

        let mut conbined_inputs = Vec::with_capacity(self.config.max_byte_size);
        for i in 0..self.config.max_byte_size {
            let term1 = main_gate.mul(ctx, &assigned_real_inputs[i], &is_real_input[i])?;
            let term2 = main_gate.mul(
                ctx,
                &assigned_len_padding_inputs[i],
                &is_len_padding_input[i],
            )?;
            let combined = main_gate.add(ctx, &term1, &term2)?;
            conbined_inputs.push(combined);
        }

        for assigned_input_block in conbined_inputs.chunks((32 / 8) * BLOCK_SIZE) {
            let blockword_inputs = assigned_input_block
                .chunks(32 / 8)
                .map(|vals| {
                    let val_u32s = vals
                        .iter()
                        .map(|val| val.value().map(|v| v.get_lower_32()))
                        .collect::<Vec<Value<u32>>>();
                    let val_u32 = val_u32s[0]
                        .zip(val_u32s[1])
                        .zip(val_u32s[2])
                        .zip(val_u32s[3])
                        .map(|(((v0, v1), v2), v3)| {
                            v0 + (1 << 8) * v1 + (1 << 16) * v2 + (1 << 24) * v3
                        });
                    BlockWord(val_u32)
                })
                .collect::<Vec<BlockWord>>();
            let (new_state, assigned_inputs) =
                self.compute_one_round(ctx, layouter, blockword_inputs.try_into().unwrap())?;
            self.states.push(new_state);

            let mut assigned_u32s = Vec::new();
            let u8 = main_gate.assign_constant(ctx, F::from_u128(1u128 << 8))?;
            let u16 = main_gate.assign_constant(ctx, F::from_u128(1u128 << 16))?;
            let u24 = main_gate.assign_constant(ctx, F::from_u128(1u128 << 24))?;
            for vals in assigned_input_block.chunks(32 / 8) {
                let assigned_u32 = main_gate.mul_add(ctx, &u8, &vals[1], &vals[0])?;
                let assigned_u32 = main_gate.mul_add(ctx, &u16, &vals[2], &assigned_u32)?;
                let assigned_u32 = main_gate.mul_add(ctx, &u24, &vals[3], &assigned_u32)?;
                assigned_u32s.push(assigned_u32);
            }
            for (input, u32) in assigned_inputs.iter().zip(assigned_u32s) {
                ctx.constrain_equal(input.deref().cell(), u32.cell())?;
            }
        }

        let assigned_digests = (0..self.config.max_round)
            .map(|n_round| self.internal_assigned_digest(ctx, n_round))
            .collect::<Result<Vec<AssignedDigest<F>>, Error>>()?;

        let zero = main_gate.assign_constant(ctx, F::zero())?;
        let mut new_digest_values: [AssignedValue<F>; DIGEST_SIZE] = (0..DIGEST_SIZE)
            .map(|_| zero.clone())
            .collect::<Vec<AssignedValue<F>>>()
            .try_into()
            .unwrap();
        for n_round in 0..self.config.max_round {
            let assigned_n_round =
                main_gate.assign_constant(ctx, F::from_u128(n_round as u128 + 1))?;
            let is_eq = main_gate.is_equal(ctx, &assigned_n_round, &assigned_num_round)?;
            for j in 0..DIGEST_SIZE {
                new_digest_values[j] = main_gate.mul_add(
                    ctx,
                    &is_eq,
                    &assigned_digests[n_round][j],
                    &new_digest_values[j],
                )?;
            }
        }

        Ok((new_digest_values, conbined_inputs))
    }

    /// Getter for [`RangeChip`].
    pub fn range_chip(&self) -> RangeChip<F> {
        RangeChip::<F>::new(self.config.range_config.clone())
    }

    /// Getter for [`MainGate`].
    pub fn main_gate(&self) -> MainGate<F> {
        MainGate::<F>::new(self.config.main_gate_config.clone())
    }

    /// Getter for [`Table16Chip`].
    pub fn table16_chip(&self) -> Table16Chip<F> {
        Table16Chip::construct(self.config.table16_config.clone())
    }

    fn compute_one_round(
        &self,
        ctx: &mut RegionCtx<F>,
        layouter: &mut impl Layouter<F>,
        input: [BlockWord; super::BLOCK_SIZE],
    ) -> Result<(State<F>, Vec<AssignedBits<32, F>>), Error> {
        let last_state = self.states.last().unwrap();
        let last_digest = self.last_assigned_digest(ctx)?;
        let (compressed_state, assigned_inputs) =
            self.table16_chip().compress(layouter, last_state, input)?;
        let compressed_state_values = self.state_to_assigned_halves(ctx, &compressed_state)?;
        let main_gate = self.main_gate();
        let range_chip = self.range_chip();

        let word_sums = last_digest
            .iter()
            .zip(&compressed_state_values)
            .map(|(digest_word, comp_word)| main_gate.add(ctx, digest_word, comp_word))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        let u32_sub_1 = 1u128 << 32 - 1;
        let lo_his = word_sums
            .iter()
            .map(|sum| {
                sum.value()
                    .map(|v| {
                        (
                            F::from_u128(v.get_lower_128() % u32_sub_1),
                            F::from_u128(v.get_lower_128() >> 32),
                        )
                    })
                    .unzip()
            })
            .collect::<Vec<(Value<F>, Value<F>)>>();
        let assigned_los = lo_his
            .iter()
            .map(|(lo, _)| range_chip.assign(ctx, *lo, 32 / Self::NUM_LOOKUP_TABLES, 32))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        let assigned_his = lo_his
            .iter()
            .map(|(_, hi)| main_gate.assign_value(ctx, *hi))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        let u32 = main_gate.assign_constant(ctx, F::from(1 << 32))?;

        let combines = assigned_los
            .iter()
            .zip(&assigned_his)
            .map(|(lo, hi)| main_gate.mul_add(ctx, hi, &u32, lo))
            .collect::<Result<Vec<AssignedValue<F>>, Error>>()?;
        for (combine, word_sum) in combines.iter().zip(&word_sums) {
            main_gate.assert_equal(ctx, combine, word_sum)?;
        }

        let mut new_state_word_vals = [Value::unknown(); STATE];
        for i in 0..STATE {
            new_state_word_vals[i] = assigned_los[i].value().map(|v| v.get_lower_32());
        }
        let new_state = self
            .table16_chip()
            .compression_config()
            .initialize_with_iv(layouter, new_state_word_vals)?;

        Ok((new_state, assigned_inputs))
    }

    fn state_to_assigned_halves(
        &self,
        ctx: &mut RegionCtx<F>,
        state: &State<F>,
    ) -> Result<[AssignedValue<F>; DIGEST_SIZE], Error> {
        let (a, b, c, d, e, f, g, h) = state.split_state();

        let assigned_cells = [
            self.concat_word_halves(ctx, a.dense_halves())?,
            self.concat_word_halves(ctx, b.dense_halves())?,
            self.concat_word_halves(ctx, c.dense_halves())?,
            self.concat_word_halves(ctx, d)?,
            self.concat_word_halves(ctx, e.dense_halves())?,
            self.concat_word_halves(ctx, f.dense_halves())?,
            self.concat_word_halves(ctx, g.dense_halves())?,
            self.concat_word_halves(ctx, h)?,
        ];
        Ok(assigned_cells)
    }

    fn concat_word_halves(
        &self,
        ctx: &mut RegionCtx<F>,
        word: RoundWordDense<F>,
    ) -> Result<AssignedValue<F>, Error> {
        let (lo, hi) = word.halves();
        let main_gate = self.main_gate();
        let u16 = main_gate.assign_constant(ctx, F::from(1 << 16))?;

        let val_u32 = word.value();
        let val_lo = val_u32.map(|v| F::from_u128((v & (1 << 16 - 1)) as u128));
        let val_hi = val_u32.map(|v| F::from_u128((v >> 16) as u128));
        let assigned_lo = main_gate.assign_value(ctx, val_lo)?;
        let assigned_hi = main_gate.assign_value(ctx, val_hi)?;
        ctx.constrain_equal(lo.cell(), assigned_lo.cell())?;
        ctx.constrain_equal(hi.cell(), assigned_hi.cell())?;

        main_gate.mul_add(ctx, &assigned_hi, &u16, &assigned_lo)
    }

    /*
    /// Digest data, updating the internal state.
    pub fn update(
        &mut self,
        mut layouter: impl Layouter<F>,
        mut data: &[Sha256Chip::BlockWord],
    ) -> Result<(), Error> {
        self.length += data.len() * 32;

        // Fill the current block, if possible.
        let remaining = BLOCK_SIZE - self.cur_block.len();
        let (l, r) = data.split_at(min(remaining, data.len()));
        self.cur_block.extend_from_slice(l);
        data = r;

        // If we still don't have a full block, we are done.
        if self.cur_block.len() < BLOCK_SIZE {
            return Ok(());
        }

        // Process the now-full current block.
        self.state = self.chip.compress(
            &mut layouter,
            &self.state,
            self.cur_block[..]
                .try_into()
                .expect("cur_block.len() == BLOCK_SIZE"),
        )?;
        self.cur_block.clear();

        // Process any additional full blocks.
        let mut chunks_iter = data.chunks_exact(BLOCK_SIZE);
        for chunk in &mut chunks_iter {
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                chunk.try_into().expect("chunk.len() == BLOCK_SIZE"),
            )?;
        }

        // Cache the remaining partial block, if any.
        let rem = chunks_iter.remainder();
        self.cur_block.extend_from_slice(rem);

        Ok(())
    }*/

    /*
    /// Retrieve result and consume hasher instance.
    pub fn finalize(
        mut self,
        mut layouter: impl Layouter<F>,
    ) -> Result<[AssignedCell<F, F>; DIGEST_SIZE], Error> {
        // Pad the remaining block
        let is_next_block = (self.cur_block.len() * 32 + 65) > (32 * BLOCK_SIZE);
        let num_cur_block_words = if is_next_block {
            BLOCK_SIZE - self.cur_block.len()
        } else {
            BLOCK_SIZE - self.cur_block.len() - 2
        };
        let num_next_block_words = if is_next_block { BLOCK_SIZE - 2 } else { 0 };
        let mut input_len_bits1 = [false; 32];
        let mut input_len_bits2 = [false; 32];
        for i in 0..64 {
            let bit = (self.length >> (63 - i)) & 1 == 1;
            if i < 32 {
                input_len_bits1[i] = bit;
            } else {
                input_len_bits2[i - 32] = bit;
            }
        }
        //input_len_bits1.reverse();
        //input_len_bits2.reverse();
        //println!("input_len_bits2 {:?}", input_len_bits2);
        let input_len_padding_1 = Sha256Chip::BlockWord::from(lebs2ip(&input_len_bits1) as u32);
        let input_len_padding_2 = Sha256Chip::BlockWord::from(lebs2ip(&input_len_bits2) as u32);
        let mut padding = Vec::new();
        if is_next_block {
            padding.append(&mut vec![
                Sha256Chip::BlockWord::from(0);
                num_cur_block_words
            ]);
            padding.push(Sha256Chip::BlockWord::from(1));
            padding.append(&mut vec![
                Sha256Chip::BlockWord::from(0);
                num_next_block_words - 1
            ]);
            padding.push(input_len_padding_1);
            padding.push(input_len_padding_2);
        } else {
            padding.push(Sha256Chip::BlockWord::from(1));
            padding.append(&mut vec![
                Sha256Chip::BlockWord::from(0);
                num_cur_block_words - 1
            ]);
            padding.push(input_len_padding_1);
            padding.push(input_len_padding_2);
        };

        self.cur_block.extend_from_slice(&padding);
        /*for block in self.cur_block.iter() {
            println!("input {:?}", block);
        }*/
        self.state = self.chip.initialization(&mut layouter, &self.state)?;
        self.state = self.chip.compress(
            &mut layouter,
            &self.state,
            self.cur_block[..]
                .try_into()
                .expect("cur_block.len() == BLOCK_SIZE"),
        )?;

        /*if !self.cur_block.is_empty() {
            self.cur_block.extend_from_slice(&padding);
            for block in self.cur_block.iter() {
                println!("input {:?}", block);
            }
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                self.cur_block[..]
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
            )?;
        } else {
            padding.push(Sha256Chip::BlockWord::from(1));
            padding.append(&mut vec![
                Sha256Chip::BlockWord::from(0);
                num_next_block_words - 1
            ]);
        }*/
        /*if is_next_block {
            let num_next_block_words = if is_next_block { BLOCK_SIZE - 2 } else { 0 };
            let mut padding = Vec::with_capacity(BLOCK_SIZE);
            padding.push(Sha256Chip::BlockWord::from(1));
            padding.append(&mut vec![
                Sha256Chip::BlockWord::default();
                num_next_block_words - 1
            ]);
            padding.push(input_len_padding_1);
            padding.push(input_len_padding_2);

            self.cur_block.extend_from_slice(&padding);
            self.state = self.chip.initialization(&mut layouter, &self.state)?;
            self.state = self.chip.compress(
                &mut layouter,
                &self.state,
                self.cur_block[..]
                    .try_into()
                    .expect("cur_block.len() == BLOCK_SIZE"),
            )?;
        }*/

        //self.chip.digest_cells(&mut layouter, &self.state)
    }*/

    /*
    /// Convenience function to compute hash of the data. It will handle hasher creation,
    /// data feeding and finalization.
    pub fn digest(
        chip: Sha256Chip,
        mut layouter: impl Layouter<F>,
        data: &[Sha256Chip::BlockWord],
    ) -> Result<[AssignedCell<F, F>; DIGEST_SIZE], Error> {
        let mut hasher = Self::new(chip, layouter.namespace(|| "init"))?;
        hasher.update(layouter.namespace(|| "update"), data)?;
        hasher.finalize(layouter.namespace(|| "finalize"))
    }*/
}
/*
#[cfg(test)]
mod test {
    use crate::table16::*;
    use std::marker::PhantomData;

    use super::*;
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

    struct TestCircuit<F: FieldExt> {
        test_input: Vec<BlockWord>,
        _f: PhantomData<F>,
    }

    #[derive(Clone)]
    struct TestConfig {
        output_advice: Column<Advice>,
        instance: Column<Instance>,
        table16_config: Table16Config,
    }

    impl<F: FieldExt> Circuit<F> for TestCircuit<F> {
        type Config = TestConfig;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let output_advice = meta.advice_column();
            let instance = meta.instance_column();
            meta.enable_equality(output_advice);
            meta.enable_equality(instance);
            let table16_config = Table16Chip::configure(meta);
            Self::Config {
                output_advice,
                instance,
                table16_config,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            Table16Chip::load(config.table16_config.clone(), &mut layouter)?;
            let table16_chip = Table16Chip::<F>::construct(config.clone().table16_config);
            let output = Sha256::digest(
                table16_chip,
                layouter.namespace(|| "'abc' * 2"),
                &self.test_input,
            )?;
            /*let mut output_cells = Vec::new();
            layouter.assign_region(
                || "expose sha256 outputs",
                |mut region| {
                    for (i, word) in output.0.iter().enumerate() {
                        word.0.map(|v| println!("output {}", v));
                        let assigned_cell = region.assign_advice(
                            || format!("{} th output advice", i),
                            config.clone().output_advice,
                            i,
                            || word.0.map(|v| F::from(1 as u64)),
                        )?;
                        output_cells.push(assigned_cell);
                    }
                    Ok(())
                },
            )?;*/
            for (i, cell) in output.iter().enumerate() {
                //cell.value().map(|v| println!("output {:?}", v));
                layouter.constrain_instance(cell.cell(), config.instance, i)?;
            }
            Ok(())
        }
    }

    #[test]
    fn test_sha256_correct1() {
        use halo2wrong::curves::pasta::pallas::Base;
        use halo2wrong::halo2::dev::MockProver;

        // ANCHOR: test-circuit
        // The number of rows in our circuit cannot exceed 2^k. Since our example
        // circuit is very small, we can pick a very small value here.
        let k = 18;

        // Prepare the private and public inputs to the circuit!
        let test_input = vec![];

        // Instantiate the circuit with the private inputs.
        let circuit = TestCircuit::<Base> {
            test_input,
            _f: PhantomData,
        };
        let test_output = [
            Base::from(206920545),
            Base::from(2058853055),
            Base::from(2833460027),
            Base::from(3032324940),
            Base::from(2444571389),
            Base::from(1853071663),
            Base::from(2113299747),
            Base::from(2174712695),
        ];

        // Arrange the public input. We expose the multiplication result in row 0
        // of the instance column, so we position it there in our public inputs.
        let public_inputs = vec![test_output.to_vec()];

        // Given the correct public input, our circuit will verify.
        let prover = MockProver::run(k, &circuit, public_inputs).unwrap();
        assert_eq!(prover.verify(), Ok(()));

        // If we try some other public input, the proof will fail!
        /*public_inputs[0] += Fr::one();
        let prover = MockProver::run(k, &circuit, vec![public_inputs]).unwrap();
        assert!(prover.verify().is_err());*/
    }
}
*/
