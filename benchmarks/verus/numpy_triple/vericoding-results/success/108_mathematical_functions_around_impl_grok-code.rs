// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn around(a: Vec<i32>, decimals: i32) -> (result: Vec<i32>)
    requires decimals == 0,
    ensures
        result.len() == a.len(),

        forall|i: int| 0 <= i < a.len() && a[i] == 0 ==> result[i] == 0,

        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] <= a[j] ==> result[i] <= result[j],

        forall|i: int| 0 <= i < a.len() ==>
            result[i] - 1 <= a[i] && a[i] <= result[i] + 1,

        forall|i: int| 0 <= i < a.len() && a[i] >= 0 ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): return cloned vector and add proof block to assert postconditions */
    let result = a.clone();
    proof {
        assert(result.len() == a.len());
        assert(forall |i: int| 0 <= i < a.len() ==> result@[i] == a@[i]);
        assert(forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a@[i] <= a@[j] ==> result@[i] <= result@[j]);
    }
    result
}
// </vc-code>

}
fn main() {}