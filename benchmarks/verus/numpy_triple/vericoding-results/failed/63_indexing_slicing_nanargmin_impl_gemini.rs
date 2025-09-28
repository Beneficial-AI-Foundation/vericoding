// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn f32_is_nan(x: f32) -> bool;
spec fn f32_le(a: f32, b: f32) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [added wrapper functions for f32 operations and fixed return type] */
#[verifier::external_body]
fn is_nan_exec(x: f32) -> (b: bool)
    ensures b == f32_is_nan(x)
{
    x.is_nan()
}

#[verifier::external_body]
fn lt_exec(a: f32, b: f32) -> (res: bool)
    ensures res == (f32_le(a, b) && !f32_le(b, a))
{
    a < b
}

fn find_first_non_nan_index(a: &Vec<f32>) -> (result: usize)
    requires
        a.len() > 0,
        exists|i: int| 0 <= i < a@.len() && !f32_is_nan(a@[i]),
    ensures
        result < a@.len(),
        !f32_is_nan(a@[result as int]),
        forall|j: int| 0 <= j < (result as int) ==> f32_is_nan(a@[j]),
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < (i as int) ==> f32_is_nan(a@[j]),
        decreases a.len() - i
    {
        if !is_nan_exec(a[i]) {
            return i;
        }
        i = i + 1;
    }
    proof {
        let k = choose|k: int| 0 <= k < a@.len() && !f32_is_nan(a@[k]);
        assert(f32_is_nan(a@[k])); // From loop invariant where i = a.len()
        assert(false); // Contradicts the choice of k
    }
    unreached()
}

// </vc-helpers>

// <vc-spec>
fn nanargmin(a: Vec<f32>) -> (result: usize)
    requires 
        a.len() > 0,
        exists|i: int| 0 <= i < a.len() && !f32_is_nan(a[i]),
    ensures
        result < a.len(),
        !f32_is_nan(a[result as int]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) ==> f32_le(a[result as int], a[j]),
        forall|j: int| 0 <= j < a.len() && !f32_is_nan(a[j]) && f32_le(a[j], a[result as int]) && f32_le(a[result as int], a[j]) ==> result as int <= j,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): [used helper functions to connect spec and exec code] */
{
    let first_idx = find_first_non_nan_index(&a);
    let mut min_idx = first_idx;
    let mut i = first_idx + 1;
    while i < a.len()
        invariant
            (first_idx as int) < (i as int) <= (a@.len() as int),
            0 <= (min_idx as int) < (i as int),
            !f32_is_nan(a@[(min_idx as int)]),
            forall|j: int| 0 <= j < (first_idx as int) ==> f32_is_nan(a@[j]),
            forall|j: int| (first_idx as int) <= j < (i as int) && !f32_is_nan(a@[j]) ==> f32_le(a@[(min_idx as int)], a@[j]),
            forall|j: int| (first_idx as int) <= j < (i as int) && !f32_is_nan(a@[j]) && f32_le(a@[j], a@[(min_idx as int)]) && f32_le(a@[(min_idx as int)], a@[j]) ==> (min_idx as int) <= j,
        decreases a.len() - i
    {
        if !is_nan_exec(a[i]) && lt_exec(a[i], a[min_idx]) {
            min_idx = i;
        }
        i = i + 1;
    }
    min_idx
}

// </vc-code>

}
fn main() {}