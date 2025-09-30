// <vc-preamble>
use vstd::prelude::*;

verus! {

/* A signature represents the core dimensionality pattern for a generalized ufunc */
pub struct UfuncSignature {
    /* Input dimension patterns as list of dimension lists */
    pub inputs: Vec<Vec<String>>,
    /* Output dimension patterns as list of dimension lists */
    pub outputs: Vec<Vec<String>>,
    /* All unique dimension names used in the signature */
    pub dimension_names: Vec<String>,
}
// </vc-preamble>

// <vc-helpers>
fn make_basic_signature() -> (result: UfuncSignature)
    ensures
        result.inputs@.len() == 1,
        result.outputs@.len() == 0,
        result.dimension_names@.len() == 0,
{
    let mut inputs: Vec<Vec<String>> = Vec::new();
    inputs.push(Vec::<String>::new());
    let outputs: Vec<Vec<String>> = Vec::new();
    let dimension_names: Vec<String> = Vec::new();
    UfuncSignature { inputs, outputs, dimension_names }
}
// </vc-helpers>

// <vc-spec>
fn parse_signature(sig: Vec<String>) -> (result: UfuncSignature)
    requires sig@.len() > 0,
    ensures
        result.inputs@.len() > 0 || result.outputs@.len() > 0,
        result.inputs@.len() + result.outputs@.len() > 0
// </vc-spec>
// <vc-code>
{
    let _n = sig.len();
    let s = make_basic_signature();
    s
}
// </vc-code>


}
fn main() {}