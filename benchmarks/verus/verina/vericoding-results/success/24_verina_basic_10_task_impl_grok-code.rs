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
    /* code modified by LLM (iteration 3): added decreases clause to while loop for termination, and fixed syntax to return true after loop */
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> n > a@[j],
        decreases a.len() - i
    {
        if !(n > a[i]) {
            return false;
        }
        i += 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}