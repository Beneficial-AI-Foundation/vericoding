use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed
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
    let mut pos: usize = 0;
    let mut i: usize = 0;
    
    // Find the first occurrence to initialize pos
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            i == 0 || (0 <= pos < i && a[pos as int] == elem),
            i > 0 ==> exists|j: int| 0 <= j < i && a[j] == elem,
    {
        if a[i as int] == elem {
            pos = i;
            i = i + 1;
            break;
        }
        i = i + 1;
    }
    
    // Continue searching for later occurrences
    while i < a.len()
        invariant
            0 <= pos < a.len(),
            0 <= i <= a.len(),
            a[pos as int] == elem,
            forall|j: int| pos < j < i ==> a[j] != elem,
    {
        if a[i as int] == elem {
            pos = i;
        }
        i = i + 1;
    }
    
    pos
}
// </vc-code>

fn main() {}
}