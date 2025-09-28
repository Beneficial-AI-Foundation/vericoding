// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn ntypes(ufunc_type_combinations: Vec<String>) -> (result: usize)
    requires ufunc_type_combinations@.len() > 0,
    ensures 
        result == ufunc_type_combinations@.len(),
        result > 0
// </vc-spec>
// <vc-code>
{
    let l = ufunc_type_combinations.len();
    l
}
// </vc-code>

}
fn main() {}