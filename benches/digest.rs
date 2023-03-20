use eth_types::Field;
use halo2_base::halo2_proofs::{
    circuit::{AssignedCell, Cell, Layouter, Region, SimpleFloorPlanner, Value},
    halo2curves::bn256::{Bn256, Fr},
    plonk::{
        create_proof, keygen_pk, keygen_vk, Advice, Circuit, Column, ConstraintSystem, Error,
        Expression, Fixed, Selector, TableColumn, VirtualCells,
    },
    poly::{
        commitment::{Params, ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::ProverGWC,
        },
        Rotation,
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
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
use zkevm_circuits::sha256_circuit::sha256_compression::{
    Sha256AssignedRows, Sha256CompressionConfig,
};

use rand::rngs::OsRng;
use rand::{thread_rng, Rng};

use std::{
    fs::File,
    io::{prelude::*, BufReader},
    path::Path,
};

use std::marker::PhantomData;

use criterion::{criterion_group, criterion_main, Criterion};

use halo2_base::{gates::range::RangeStrategy::Vertical, SKIP_FIRST_PASS};
use halo2_dynamic_sha256::Sha256DynamicConfig;

const K: u32 = 11;

fn bench(name: &str, k: u32, c: &mut Criterion) {
    #[derive(Debug, Clone)]
    struct BenchCircuit<F: Field> {
        test_input: Vec<u8>,
        _f: PhantomData<F>,
    }

    impl<F: Field> Circuit<F> for BenchCircuit<F> {
        type Config = Sha256DynamicConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let sha256_bit_configs = vec![Sha256CompressionConfig::configure(meta)];
            let range_config = RangeConfig::configure(
                meta,
                Vertical,
                &[Self::NUM_ADVICE],
                &[Self::NUM_LOOKUP_ADVICE],
                Self::NUM_FIXED,
                Self::LOOKUP_BITS,
                0,
                K as usize,
            );
            let sha256 = Sha256DynamicConfig::construct(
                sha256_bit_configs,
                Self::MAX_BYTE_SIZE,
                range_config,
            );
            sha256
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let sha256 = config;
            let range = sha256.range().clone();
            range.load_lookup_table(&mut layouter)?;
            let mut first_pass = SKIP_FIRST_PASS;
            layouter.assign_region(
                || "random rsa modpow test with 2048 bits public keys",
                |region| {
                    if first_pass {
                        first_pass = false;
                        return Ok(());
                    }

                    let ctx = &mut sha256.new_context(region);
                    let _ = sha256.digest(ctx, &self.test_input)?;
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
            Ok(())
        }
    }

    impl<F: Field> BenchCircuit<F> {
        const MAX_BYTE_SIZE: usize = 1024;
        const NUM_ADVICE: usize = 50;
        const NUM_FIXED: usize = 1;
        const NUM_LOOKUP_ADVICE: usize = 1;
        const LOOKUP_BITS: usize = 8;
    }

    // Initialize the polynomial commitment parameters
    let params_name = format!("./benches/sha256_params_{}", k);
    let params_path = Path::new(&params_name);
    if File::open(&params_path).is_err() {
        let params: ParamsKZG<Bn256> = ParamsKZG::new(k);
        let mut buf = Vec::new();

        params.write(&mut buf).expect("Failed to write params");
        let mut file = File::create(&params_path).expect("Failed to create sha256_params");

        file.write_all(&buf[..])
            .expect("Failed to write params to file");
    }

    let params_fs = File::open(&params_path).expect("couldn't load sha256_params");
    let params: ParamsKZG<Bn256> =
        ParamsKZG::read::<_>(&mut BufReader::new(params_fs)).expect("Failed to read params");

    let test_input = vec![0; 60];
    // let output = Sha256::digest(&test_input);
    // let output = output
    //     .into_iter()
    //     .map(|byte| Fr::from(byte as u64))
    //     .collect::<Vec<Fr>>();
    let circuit = BenchCircuit {
        test_input: test_input.clone(),
        _f: PhantomData,
    };

    // Initialize the proving key
    let vk = keygen_vk(&params, &circuit).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &circuit).expect("keygen_pk should not fail");

    let prover_name = name.to_string() + "-prover";
    let verifier_name = name.to_string() + "-verifier";

    // Benchmark proof creation
    c.bench_function(&prover_name, |b| {
        b.iter(|| {
            let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
            create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
                &params,
                &pk,
                &[circuit.clone()],
                &[&[]],
                OsRng,
                &mut transcript,
            )
            .expect("proof generation should not fail");
            let _: Vec<u8> = transcript.finalize();
        });
    });

    // Create a proof
    // let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    // create_proof::<KZGCommitmentScheme<_>, ProverGWC<_>, _, _, _, _>(
    //     &params,
    //     &pk,
    //     &[circuit],
    //     &[&[&output]],
    //     OsRng,
    //     &mut transcript,
    // )
    // .expect("proof generation should not fail");
    // let proof: Vec<u8> = transcript.finalize();

    // c.bench_function(&verifier_name, |b| {
    //     b.iter(|| {
    //         let strategy = SingleStrategy::new(&params);
    //         let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    //         assert!(verify_proof::<_, VerifierGWC<_>, _, _, _>(
    //             &params,
    //             pk.get_vk(),
    //             strategy,
    //             &[&[&output]],
    //             &mut transcript
    //         )
    //         .is_ok());
    //     });
    // });
}

fn criterion_benchmark(c: &mut Criterion) {
    bench("sha256", K, c);
    // bench("sha256", 20, c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
