// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [No helpers needed for this problem] */
// </vc-helpers>

// <vc-spec>
spec fn is_non_zero_vector(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn floor_divide(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == b.len(),
        is_non_zero_vector(a@.map(|i, x: i8| x as i32)),
        is_non_zero_vector(b@.map(|i, x: i8| x as i32)),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as i32 == (a[i] as i32) / (b[i] as i32),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [Changed `result[j as usize]` to `result@[j]` to fix type mismatching `usize` with `int` in the `forall` clause of the loop invariant.] */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as i32 == (a@[j] as i32) / (b@[j] as i32),

    {
        result.push((a[i] as i32 / b[i] as i32) as i8);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}