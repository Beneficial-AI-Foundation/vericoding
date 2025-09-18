// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `while` loop condition to use `usize` arithmetic to fix compilation errors. */
{
    let mut i: usize = 0;
    while i + 1 < a.len()
        invariant
            0 <= i as int,
            i < a.len(),
            forall|j: int| 0 <= j < i as int ==> a[j as usize] + 1 != a[(j + 1) as usize],
        decreases a.len() - (i + 1)
    {
        if a[i] + 1 == a[i + 1] {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}