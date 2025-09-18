// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn len_of_vec(v: Vec<String>) -> usize { v.len() }
// </vc-helpers>

// <vc-spec>
fn ntypes(ufunc_type_combinations: Vec<String>) -> (result: usize)
    requires ufunc_type_combinations.len() > 0,
    ensures 
        result == ufunc_type_combinations.len(),
        result > 0
// </vc-spec>
// <vc-code>
{
    let result = ufunc_type_combinations.len();
    proof {
        assert(result == ufunc_type_combinations.len());
        assert(ufunc_type_combinations.len() > 0);
        assert(result > 0);
    }
    result
}
// </vc-code>

}
fn main() {}