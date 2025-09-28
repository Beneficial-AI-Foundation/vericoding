// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &Vec<i32>) -> (result: bool)
    requires a.len() > 0,
    ensures result == (forall|i: int| 0 <= i < a.len() ==> n > a[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added decreases clause to the while loop to ensure termination and complete the verification for the forall postcondition. */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            forall|j: int| 0 <= j < i ==> n > a[j],
            i <= a.len(),
        decreases a.len() - i
    {
        if n <= a[i] {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}