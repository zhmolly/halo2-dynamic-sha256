use std::{cell::RefCell, collections::HashMap, marker::PhantomData};

use halo2_base::{
    gates::{
        builder::{CircuitBuilderStage, FlexGateConfigParams, MultiPhaseThreadBreakPoints},
        range::{RangeConfig, RangeStrategy},
    },
    utils::ScalarField,
    SKIP_FIRST_PASS,
    halo2_proofs::{
        circuit::{self, Layouter, SimpleFloorPlanner},
        plonk::{Circuit, ConstraintSystem, Error},
    }
};

use crate::{gate::ShaThreadBuilder, spread::SpreadConfig};

#[derive(Debug, Clone)]
pub struct SHAConfig<F: ScalarField> {
    pub compression: SpreadConfig<F>,
    pub range: RangeConfig<F>,
}

impl<F: ScalarField> SHAConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, params: FlexGateConfigParams) -> Self {
        let degree = params.k;
        let mut range = RangeConfig::configure(
            meta,
            RangeStrategy::Vertical,
            &params.num_advice_per_phase,
            &params.num_lookup_advice_per_phase,
            params.num_fixed,
            params.k - 1,
            degree,
        );
        let compression = SpreadConfig::configure(meta, 8, 1);

        range.gate.max_rows = (1 << degree) - meta.minimum_rows();
        Self { range, compression }
    }
}

pub struct ShaCircuitBuilder<F: ScalarField> {
    pub builder: RefCell<ShaThreadBuilder<F>>,
    pub break_points: RefCell<MultiPhaseThreadBreakPoints>, // `RefCell` allows the circuit to record break points in a keygen call of `synthesize` for use in later witness gen
    _f: PhantomData<F>,
}

impl<F: ScalarField> ShaCircuitBuilder<F> {
    pub fn new(
        builder: ShaThreadBuilder<F>,
        break_points: Option<MultiPhaseThreadBreakPoints>,
    ) -> Self {
        Self {
            builder: RefCell::new(builder),
            break_points: RefCell::new(break_points.unwrap_or_default()),
            _f: PhantomData,
        }
    }

    pub fn from_stage(
        builder: ShaThreadBuilder<F>,
        break_points: Option<MultiPhaseThreadBreakPoints>,
        stage: CircuitBuilderStage,
    ) -> Self {
        Self::new(
            builder.unknown(stage == CircuitBuilderStage::Keygen),
            break_points,
        )
    }

    /// Creates a new [ShaCircuitBuilder] with `use_unknown` of [ShaThreadBuilder] set to true.
    pub fn keygen(builder: ShaThreadBuilder<F>) -> Self {
        Self::new(builder.unknown(true), None)
    }

    /// Creates a new [ShaCircuitBuilder] with `use_unknown` of [GateThreadBuilder] set to false.
    pub fn mock(builder: ShaThreadBuilder<F>) -> Self {
        Self::new(builder.unknown(false), None)
    }

    /// Creates a new [ShaCircuitBuilder].
    pub fn prover(builder: ShaThreadBuilder<F>, break_points: MultiPhaseThreadBreakPoints) -> Self {
        Self::new(builder.unknown(false), Some(break_points))
    }

    pub fn config(&self, k: usize, minimum_rows: Option<usize>) -> FlexGateConfigParams {
        // clone everything so we don't alter the circuit in any way for later calls
        let mut builder = self.builder.borrow().clone();
        builder.config(k, minimum_rows)
    }

    // re-usable function for synthesize
    #[allow(clippy::type_complexity)]
    pub fn sub_synthesize(
        &self,
        config: &SHAConfig<F>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<HashMap<(usize, usize), (circuit::Cell, usize)>, Error> {
        config
            .range
            .load_lookup_table(layouter)
            .expect("load range lookup table");

        let mut first_pass = SKIP_FIRST_PASS;
        let witness_gen_only = self.builder.borrow().witness_gen_only();

        let mut assigned_advices = HashMap::new();

        config.compression.load(layouter)?;

        layouter.assign_region(
            || "ShaCircuitBuilder generated circuit",
            |mut region| {
                if first_pass {
                    first_pass = false;
                    return Ok(());
                }

                if !witness_gen_only {
                    let mut builder = self.builder.borrow().clone();

                    let assignments = builder.assign_all(
                        &config.range.gate,
                        &config.range.lookup_advice,
                        &config.range.q_lookup,
                        &config.compression,
                        &mut region,
                        Default::default(),
                    )?;
                    *self.break_points.borrow_mut() = assignments.break_points.clone();
                    assigned_advices = assignments.assigned_advices;
                } else {
                    let builder = &mut self.builder.borrow_mut();
                    let break_points = &mut self.break_points.borrow_mut();

                    builder.assign_witnesses(
                        &config.range.gate,
                        &config.range.lookup_advice,
                        &config.compression,
                        &mut region,
                        break_points,
                    )?;
                }
                Ok(())
            },
        )?;
        Ok(assigned_advices)
    }
}

impl<F: ScalarField> Circuit<F> for ShaCircuitBuilder<F> {
    type Config = SHAConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> SHAConfig<F> {
        let params: FlexGateConfigParams =
            serde_json::from_str(&std::env::var("FLEX_GATE_CONFIG_PARAMS").unwrap()).unwrap();
        SHAConfig::configure(meta, params)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        self.sub_synthesize(&config, &mut layouter)?;
        Ok(())
    }
}
