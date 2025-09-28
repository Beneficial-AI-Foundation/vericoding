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
    /* code modified by LLM (iteration 2): Added decreases clause to outer while loop */
    let mut result = Vec::new();
    let mut rep_count = 0;
    
    while rep_count < reps
        invariant
            rep_count <= reps,
            result.len() == rep_count * a.len(),
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
        decreases reps - rep_count
    {
        let mut j = 0;
        while j < a.len()
            invariant
                j <= a.len(),
                result.len() == rep_count * a.len() + j,
                forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
            decreases a.len() - j
        {
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