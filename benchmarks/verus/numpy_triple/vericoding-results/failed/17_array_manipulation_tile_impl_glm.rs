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
/* code modified by LLM (iteration 2): changed loop variable to usize to avoid ghost type usage */
{
    let n = a.len();
    let total = n * reps;
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < total
        invariant
            i <= total,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] == a@[j % (n as int)],
        decreases total - i
    {
        let index_in_a = i % n;
        result.push(a[index_in_a]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}