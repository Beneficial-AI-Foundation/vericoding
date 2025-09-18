// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): normalized positive modulo helper */
spec fn idx_mod(a_len: usize, i: int) -> int { if a_len == 0 { 0 } else { let am: int = a_len as int; let r: int = i % am; if r < 0 { r + am } else { r } } }
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
    /* code modified by LLM (iteration 5): implement tiling with loop invariants and correct syntax */
    let mut result: Vec<i32> = Vec::new();
    let alen: usize = a.len();
    let mut r: usize = 0;
    while r < reps
        invariant result.len() == alen * r
        invariant (forall |i: int| 0 <= i && i < (result.len() as int) ==> result[i as usize] == a[(idx_mod(alen, i)) as usize])
        decreases reps - r
    {
        let mut j: usize = 0;
        while j < alen
            invariant j <= alen
            invariant result.len() == alen * r + j
            invariant (forall |i: int| 0 <= i && i < (result.len() as int) ==> result[i as usize] == a[(idx_mod(alen, i)) as usize])
            decreases alen - j
        {
            result.push(a[j]);
            j = j + 1;
        }
        r = r + 1;
    }
    result
}
// </vc-code>

}
fn main() {}