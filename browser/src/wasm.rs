// wasm_bindgen_rayon requires the rustflags defined in .cargo/config
// to be set in order to compile. When we enable rustflags,
// rust-analyzer (the vscode extension) stops working, so by default,
// we don't compile wasm_bindgen_rayon which requires rustflags,
#[cfg(target_family = "wasm")]
pub use wasm_bindgen_rayon::init_thread_pool;

// circuit code
use crate::circuits::ecc_circuit::EccCircuit;
use crate::circuits::simple_circuit::SimpleCircuit;

// WASM/browser specific
use serde_wasm_bindgen;
use wasm_bindgen::prelude::*;
use web_sys;

// necessary code for boiler plate proving
use halo2_proofs::pasta::EqAffine;
use halo2_proofs::plonk::{
    create_proof, create_proof_profile, keygen_pk, keygen_vk, verify_proof, SingleVerifier,
};
use halo2_proofs::poly::commitment::Params;
use halo2_proofs::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
use js_sys::Uint8Array;
use rand_core::OsRng;
use std::io::BufReader;

// A macro to provide `println!(..)`-style syntax for `console.log` logging.
macro_rules! log {
    ( $( $t:tt )* ) => {
        web_sys::console::log_1(&format!( $( $t )* ).into());
    }
}

#[wasm_bindgen]
pub fn init_panic_hook() {
    console_error_panic_hook::set_once();
}

#[wasm_bindgen]
pub fn prove_simple_circuit(params_ser: JsValue) -> JsValue {
    let empty_circuit = SimpleCircuit {};

    web_sys::console::time_with_label("load params");
    let params_vec = Uint8Array::new(&params_ser).to_vec();
    let params: Params<EqAffine> = Params::read(&mut BufReader::new(&params_vec[..])).unwrap();
    web_sys::console::time_end_with_label("load params");

    web_sys::console::time_with_label("vkey generation");
    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    web_sys::console::time_end_with_label("vkey generation");

    web_sys::console::time_with_label("pkey generation");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");
    web_sys::console::time_end_with_label("pkey generation");

    let circuit = SimpleCircuit {};

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    web_sys::console::time_with_label("proof generation");
    create_proof_profile(
        &params,
        &pk,
        &[circuit],
        &[&[]],
        OsRng,
        &mut transcript,
        &web_sys::console::time_with_label,
        &web_sys::console::time_end_with_label,
        &web_sys::console::count_with_label,
    )
    .expect("proof generation should not fail");

    let proof: Vec<u8> = transcript.finalize();
    web_sys::console::time_end_with_label("proof generation");

    serde_wasm_bindgen::to_value(&proof).unwrap()
}

#[wasm_bindgen]
pub fn prove_scalar_mult(params_ser: JsValue) -> JsValue {
    let empty_circuit = EccCircuit {};

    web_sys::console::time_with_label("load params");
    let params_vec = Uint8Array::new(&params_ser).to_vec();
    let params: Params<EqAffine> = Params::read(&mut BufReader::new(&params_vec[..])).unwrap();
    web_sys::console::time_end_with_label("load params");

    web_sys::console::time_with_label("vkey generation");
    let vk = keygen_vk(&params, &empty_circuit).expect("keygen_vk should not fail");
    web_sys::console::time_end_with_label("vkey generation");

    web_sys::console::time_with_label("pkey generation");
    let pk = keygen_pk(&params, vk, &empty_circuit).expect("keygen_pk should not fail");
    web_sys::console::time_end_with_label("pkey generation");

    let circuit = EccCircuit {};

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    web_sys::console::time_with_label("proof generation");
    create_proof(&params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)
        .expect("proof generation should not fail");

    let proof: Vec<u8> = transcript.finalize();
    web_sys::console::time_end_with_label("proof generation");

    serde_wasm_bindgen::to_value(&proof).unwrap()
}

#[wasm_bindgen]
pub fn prove_scalar_mult_full(params_ser: JsValue) -> JsValue {
    let empty_circuit = EccCircuit {};

    web_sys::console::time_with_label("load params");
    let params_vec = Uint8Array::new(&params_ser).to_vec();
    let params_gen: Params<EqAffine> = Params::read(&mut BufReader::new(&params_vec[..])).unwrap();
    web_sys::console::time_end_with_label("load params");

    web_sys::console::time_with_label("vkey generation");
    let vk_gen = keygen_vk(&params_gen, &empty_circuit).expect("keygen_vk should not fail");
    web_sys::console::time_end_with_label("vkey generation");

    web_sys::console::time_with_label("pkey generation");
    let pk_gen = keygen_pk(&params_gen, vk_gen, &empty_circuit).expect("keygen_pk should not fail");
    web_sys::console::time_end_with_label("pkey generation");

    let circuit = EccCircuit {};
    let mut transcript_gen = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);

    let params = &params_gen;
    let pk = &pk_gen;
    let circuits = &[circuit];
    let mut rng = OsRng;
    let instances: &[&[&[pasta_curves::Fp]]] = &[&[]];
    let transcript = &mut transcript_gen;

    web_sys::console::time_with_label("proof generation");
    create_proof_profile(
        params,
        pk,
        circuits,
        instances,
        rng,
        transcript,
        &mut web_sys::console::time_with_label,
        &mut web_sys::console::time_end_with_label,
        &mut web_sys::console::count_with_label,
    )
    .expect("proof generation should not fail");

    let proof: Vec<u8> = transcript_gen.finalize();
    web_sys::console::time_end_with_label("proof generation");

    serde_wasm_bindgen::to_value(&proof).unwrap()
}
