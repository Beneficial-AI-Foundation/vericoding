// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fix invariant initialization by finding first occurrence before loop */
    let mut pos = 0;
    let mut i = 0;
    
    // Find first occurrence to establish invariant
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] != elem,
        decreases a.len() - i
    {
        if a[i] == elem {
            pos = i;
            break;
        }
        i += 1;
    }
    
    // Continue from pos+1 to find last occurrence
    i = pos + 1;
    while i < a.len()
        invariant
            0 <= pos < a.len(),
            pos < i <= a.len(),
            a[pos as int] == elem,
            forall|j: int| pos < j < i ==> a[j] != elem,
        decreases a.len() - i
    {
        if a[i] == elem {
            pos = i;
        }
        i += 1;
    }
    pos
}
// </vc-code>

}
fn main() {}