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
{
    /* code modified by LLM (iteration 2): changed nested for loops to while loops with invariants and added bounds assertion */
    let len = a.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < reps
        invariant
            result.len() == i * len,
            forall|k: int| 0 <= k < result.len() ==> result[k] == a[k % (len as int)],
        decreases reps - i,
    {
        let mut j = 0;
        while j < len
            invariant
                result.len() == i * len + j,
                forall|k: int| 0 <= k < result.len() ==> result[k] == a[k % (len as int)],
            decreases len - j,
        {
            assert(j < len);
            result.push(a[j]);
            j = j + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}