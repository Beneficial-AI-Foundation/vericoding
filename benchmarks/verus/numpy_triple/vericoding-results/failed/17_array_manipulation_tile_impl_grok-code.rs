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
    /* code modified by LLM (iteration 5): Fixed Unicode characters for parentheses and commas in invariants */
    let mut result = Vec::new();
    let mut count = 0;
    while count < reps
        invariant
            result@.len() == (count as int) * a@.len(),
            forall|i: int| 0 <= i < result@.len() ==> result@[i] == a@[(i % a@.len())],
        decreases (reps - count) as int
    {
        let mut idx = 0;
        while idx < a.len()
            invariant
                result@.len() == (count as int) * a@.len() + (idx as int),
                forall|i: int| 0 <= i < result@.len() ==> result@[i] == a@[(i % a@.len())],
            decreases (a.len() - idx) as int
        {
            result.push(a[idx]); 
            idx += 1;
        }
        count += 1;
    }
    result
}
// </vc-code>

}
fn main() {}