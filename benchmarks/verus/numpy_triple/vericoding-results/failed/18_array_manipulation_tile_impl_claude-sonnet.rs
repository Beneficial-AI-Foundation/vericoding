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
    /* code modified by LLM (iteration 5): simplified proof and fixed modular arithmetic */
    let mut result: Vec<i32> = Vec::new();
    let mut rep = 0;
    while rep < reps
        invariant
            result.len() == a.len() * rep,
            forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
        decreases reps - rep
    {
        let mut j = 0;
        while j < a.len()
            invariant
                result.len() == a.len() * rep + j,
                forall|i: int| 0 <= i < result.len() ==> result[i] == a[i % (a.len() as int)],
            decreases a.len() - j
        {
            result.push(a[j]);
            proof {
                let new_idx = (result.len() - 1) as int;
                assert(new_idx == (a.len() * rep + j) as int);
                assert((a.len() * rep + j) % a.len() == j % a.len());
                assert(j < a.len());
                assert(j % a.len() == j);
                assert(new_idx % (a.len() as int) == j as int);
            }
            j += 1;
        }
        rep += 1;
    }
    result
}
// </vc-code>

}
fn main() {}