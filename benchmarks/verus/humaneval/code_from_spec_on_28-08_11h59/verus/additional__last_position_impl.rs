use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn last_position(a: &[i32], elem: i32) -> (result: usize)
    // pre-conditions-start
    requires
        0 < a.len() < 100_000,
        exists|i: int| 0 <= i < a.len() && a[i] == elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result < a.len(),
        forall|i: int| result < i < a.len() ==> a[i] != elem,
        a[result as int] == elem,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut pos = 0;
    let mut i = 1;
    
    // Initialize pos to the first occurrence
    while i <= a.len() && a[pos] != elem
        invariant
            0 <= pos < a.len(),
            0 <= i <= a.len() + 1,
        decreases a.len() + 1 - i
    {
        if pos + 1 < a.len() {
            pos += 1;
        }
        i += 1;
    }
    
    // Now find the last occurrence
    i = pos + 1;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            0 <= pos < a.len(),
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

fn main() {}
}