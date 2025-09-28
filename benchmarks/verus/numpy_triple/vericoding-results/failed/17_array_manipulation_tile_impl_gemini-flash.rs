// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn tile(a: Vec<i32>, reps: usize) -> (result: Vec<i32>)
    requires 
        reps > 0,
        a.len() > 0,
    ensures
        result.len() == a.len() * reps,
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type mismatches for array indexing within the loop invariant to align with `a` being indexed by `usize` type and `a_len` also being `usize` */
{
    let a_len: usize = a.len();
    let result_len: usize = a_len * reps;
    let mut result: Vec<i32> = Vec::new();
    result.reserve(result_len);

    let mut i: usize = 0;
    while i < result_len
        invariant
            0 <= i && i <= result_len,
            result.len() == i,
            forall|j: int| 0 <= j && (j as usize) < i ==> result[j as usize] == a[j as usize % a_len],
        decreases result_len - i
    {
        result.push(a[i % a_len]);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}