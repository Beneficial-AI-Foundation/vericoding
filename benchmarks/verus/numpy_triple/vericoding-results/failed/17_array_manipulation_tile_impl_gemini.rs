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
/* code modified by LLM (iteration 3): [remove explicit overflow check and infinite loop] */
{
    let a_len = a.len();
    let total_len = a_len * reps;
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < total_len
        invariant
            a_len == a.len(),
            total_len == a.len() * reps,
            i <= total_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j % (a.len() as int)],
        decreases total_len - i
    {
        result.push(a[i % a_len]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}