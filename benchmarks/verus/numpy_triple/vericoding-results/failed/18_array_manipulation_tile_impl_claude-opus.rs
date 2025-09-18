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
    /* code modified by LLM (iteration 5): Fixed modulo arithmetic and invariant maintenance */
    let mut result = Vec::new();
    let mut rep_count = 0;
    while rep_count < reps
        invariant
            rep_count <= reps,
            result.len() == a.len() * rep_count,
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
        decreases reps - rep_count
    {
        let mut j = 0;
        while j < a.len()
            invariant
                j <= a.len(),
                result.len() == a.len() * rep_count + j,
                forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
            decreases a.len() - j
        {
            let idx = (a.len() * rep_count + j) as int;
            proof {
                assert(idx % (a.len() as int) == j as int);
                assert(a[j] == a[j as int]);
            }
            result.push(a[j]);
            j = j + 1;
        }
        rep_count = rep_count + 1;
    }
    result
}
// </vc-code>

}
fn main() {}