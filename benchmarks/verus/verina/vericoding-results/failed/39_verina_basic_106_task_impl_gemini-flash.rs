// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helper functions needed for this task. */
// </vc-helpers>

// <vc-spec>
fn array_sum(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    requires a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == a[i] + b[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `old` type inference on `a` and `b` in invariants. */
{
    let mut result = Vec::new();
    let len = a.len();
    let mut i = 0;

    while i < len
        invariant
            0 <= i <= len,
            result.len() == i,
            // All elements processed so far are correct
            forall|j: int| 0 <= j < i ==> result@[j] == (a@[j] as int + b@[j] as int) as i32,
            // Elements of a remain unchanged for `len` iterations
            forall|j: int| i <= j < len ==> a@[j] == old(a)@.into_option().unwrap()[j],
            // Elements of b remain unchanged for `len` iterations
            forall|j: int| i <= j < len ==> b@[j] == old(b)@.into_option().unwrap()[j],

        decreases len - i
    {
        proof {
            // Prove that a[i] and b[i] are accessible
            assert(0 <= i && i < a.len()) by(nonlinear_arith) requires(i < len, len == a.len());
            assert(0 <= i && i < b.len()) by(nonlinear_arith) requires(i < len, len == b.len());
        }
        result.push(a[i] + b[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}