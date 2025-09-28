// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn linear_search(a: &[i32], e: i32) -> (n: usize)
    requires exists|i: int| 0 <= i < a.len() && a[i] == e,
    ensures ({
        &&& 0 <= n < a.len() 
        &&& a[n as int] == e
        &&& forall|k: int| 0 <= k < n as int ==> a[k] != e
    }),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): remove semicolon from unreached() to fix return type and add cast in loop invariant */
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int| 0 <= k < (i as int) ==> a[k] != e,
        decreases a.len() - i
    {
        if a[i] == e {
            return i;
        }
        i = i + 1;
    }
    unreached()
}
// </vc-code>

}
fn main() {}