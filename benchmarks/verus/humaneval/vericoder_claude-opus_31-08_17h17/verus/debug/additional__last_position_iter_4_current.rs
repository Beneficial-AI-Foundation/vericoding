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
    let mut found: bool = false;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            found ==> (0 <= pos < i && a[pos as int] == elem),
            found ==> forall|j: int| pos < j < i ==> a[j] != elem,
            !found ==> forall|j: int| 0 <= j < i ==> a[j] != elem,
            exists|k: int| 0 <= k < a.len() && a[k] == elem,
        decreases a.len() - i,
    {
        if a[i] == elem {
            pos = i;
            found = true;
        }
        i = i + 1;
    }
    
    assert(found) by {
        // We know from the precondition that there exists an element
        // and we've searched through the entire array
        assert(i == a.len());
        assert(exists|k: int| 0 <= k < a.len() && a[k] == elem);
        assert(forall|j: int| 0 <= j < a.len() ==> (found || a[j] != elem));
    }
    
    pos
}
// </vc-code>

fn main() {}
}