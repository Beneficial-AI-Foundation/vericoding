// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove requires/ensures from spec function that caused compilation error */
spec fn get_index_in_original(i: int, len: int) -> int {
    i % len
}

proof fn mod_lemma(i: int, len: int)
    requires
        len > 0,
    ensures
        0 <= i % len < len,
{
    assert(0 <= i % len < len) by (nonlinear_arith);
}
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
/* code modified by LLM (iteration 5): Use proper spec function call pattern & maintain verification */
{
    let len: usize = a.len();
    let mut result = Vec::new();
    let mut count: usize = 0;
    while count < reps
        invariant
            count <= reps,
            result.len() == count * len,
            forall|j: int| 0 <= j < result.len() ==> result[j] == a[get_index_in_original(j, len as int)],
        decreases reps - count,
    {
        let mut i: usize = 0;
        while i < len
            invariant
                i <= len,
                result.len() == count * len + i,
                forall|j: int| 0 <= j < result.len() ==> result[j] == a[get_index_in_original(j, len as int)],
            decreases len - i,
        {
            proof {
                mod_lemma(i as int, len as int);
            }
            result.push(a[i]);
            i += 1;
        }
        count += 1;
    }
    result
}
// </vc-code>

}
fn main() {}