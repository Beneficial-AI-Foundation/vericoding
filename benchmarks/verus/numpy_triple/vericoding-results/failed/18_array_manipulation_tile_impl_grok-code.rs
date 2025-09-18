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
    /* code modified by LLM (iteration 5): Used int for total calculation to avoid usize overflow, added proof assertions for indexing bounds, and ensured invariants and postconditions are satisfied. */
    let a_len = a.len();
    let mut result = Vec::new();
    let total_int: int = (a_len as int) * (reps as int);
    let mut i: int = 0;
    while i < total_int
        invariant
            result@.len() == i,
            i >= 0,
            total_int >= 0,
            forall|k: int| 0 <= k < i ==> result@[k] == a@[(k % (a_len as int))],
        decreases (total_int - i)
    {
        proof {
            assert(i >= 0);
            assert(a_len > 0);
            assert(0 <= i % (a_len as int) < (a_len as int));
        }
        let index_int: int = i % (a_len as int);
        let index: usize = index_int as usize;
        let val = a[index];
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}