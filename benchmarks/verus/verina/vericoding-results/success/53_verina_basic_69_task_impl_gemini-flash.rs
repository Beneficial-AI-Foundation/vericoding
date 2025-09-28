// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed unnecessary placeholders. */
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i32>, e: i32) -> (result: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures
        result < a.len(),
        a[result as int] == e,
        forall|k: int| 0 <= k < result ==> a[k] != e,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fix compilation error by replacing `unreachable!()` with `unreached()` */
{
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i,
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] != e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    // This code should not be reached due to the `exists` precondition.
    // However, Verus requires a return in all paths, so we use `unreached()`.
    unreached()
}
// </vc-code>

}
fn main() {}