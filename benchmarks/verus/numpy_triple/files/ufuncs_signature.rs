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
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}