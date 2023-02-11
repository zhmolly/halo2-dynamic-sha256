use halo2wrong::curves::bn256::{Bn256, Fr};
use halo2wrong::curves::FieldExt;
use halo2wrong::halo2::poly::kzg::{
    commitment::{KZGCommitmentScheme, ParamsKZG},
    multiopen::{ProverGWC, VerifierGWC},
    strategy::SingleStrategy,
};
use halo2wrong::halo2::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{
        create_proof, keygen_pk, keygen_vk, verify_proof, Advice, Circuit, Column,
        ConstraintSystem, Error, Instance,
    },
    poly::commitment::Params,
    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
};
use maingate::{
    big_to_fe, decompose_big, fe_to_big, AssignedValue, MainGate, MainGateConfig,
    MainGateInstructions, RangeChip, RangeConfig, RangeInstructions, RegionCtx,
};
use rand::rngs::OsRng;
use rand::{thread_rng, Rng};

use sha2::{Digest, Sha256};
use std::{
    fs::File,
    io::{prelude::*, BufReader},
    path::Path,
};

use std::marker::PhantomData;

use criterion::{criterion_group, criterion_main, Criterion};

use halo2_dynamic_sha256::{Field, Sha256BitConfig, Sha256DynamicChip, Sha256DynamicConfig};

use halo2wrong::halo2::{
    poly::commitment::ParamsProver,
    transcript::{TranscriptReadBuffer, TranscriptWriterBuffer},
};

fn bench(name: &str, k: u32, c: &mut Criterion) {
    #[derive(Debug, Clone)]
    struct BenchConfig<F: Field> {
        sha256_config: Sha256DynamicConfig<F>,
    }

    #[derive(Debug, Clone)]
    struct BenchCircuit<F: Field> {
        test_input: Vec<u8>,
        _f: PhantomData<F>,
    }

    impl<F: Field> Circuit<F> for BenchCircuit<F> {
        type Config = BenchConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            unimplemented!()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let main_gate_config = MainGate::<F>::configure(meta);
            let sha256_bit_config = Sha256BitConfig::configure(meta);
            let sha256_config = Sha256DynamicChip::configure(
                meta,
                main_gate_config,
                sha256_bit_config,
                Self::MAX_BYTE_SIZE,
            );
            Self::Config { sha256_config }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            Sha256DynamicChip::load(&config.sha256_config, &mut layouter)?;
            let sha256_chip = Sha256DynamicChip::new(config.sha256_config.clone());
            // let range_chip = sha256_chip.range_chip();
            // range_chip.load_table(&mut layouter)?;
            let (_, _, assigned_hash) = sha256_chip.digest(
                layouter.namespace(|| "sha256_dynamic_chip"),
                &self.test_input,
            )?;
            let maingate = sha256_chip.main_gate();
            for (idx, cell) in assigned_hash.into_iter().enumerate() {
                maingate.expose_public(layouter.namespace(|| "publish hash"), cell, idx)?;
            }
            Ok(())
        }
    }

    impl<F: Field> BenchCircuit<F> {
        const MAX_BYTE_SIZE: usize = 128;
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
    let output = Sha256::digest(&test_input);
    let output = output
        .into_iter()
        .map(|byte| Fr::from(byte as u64))
        .collect::<Vec<Fr>>();
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
                &[&[&output]],
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
    bench("sha256", 11, c);
    // bench("sha256", 20, c);
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
