// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers required for this problem. */
// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `a[i]` usage within `while` loop to ensure valid indexing using `i < a.len()` in loop invariant. */
{
    let len = a.len();
    let mut i: usize = 0;

    while i < len
        invariant
            0 <= i as int <= len as int,
            forall|j: int| 0 <= j < i as int ==> a[j] != key,
        decreases len - i
    {
        if i < a.len() && a[i] == key { /* Check i < a.len() to satisfy precondition for a[i] */
            return i as i32;
        }
        i = i + 1;
    }

    -1
}
// </vc-code>

}
fn main() {}