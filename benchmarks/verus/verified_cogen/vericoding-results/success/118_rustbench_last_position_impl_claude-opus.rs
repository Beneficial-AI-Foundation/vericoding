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
    /* code modified by LLM (iteration 3): fixed invariant logic for found_pos initialization and maintenance */
    let mut pos: usize = 0;
    let mut found_pos: usize = 0;
    let mut found: bool = false;
    
    while pos < a.len()
        invariant
            0 <= pos <= a.len(),
            found ==> (0 <= found_pos < pos && a[found_pos as int] == elem),
            found ==> forall|i: int| found_pos < i < pos ==> a[i] != elem,
            !found ==> forall|i: int| 0 <= i < pos ==> a[i] != elem,
            found || pos == 0 || exists|i: int| pos <= i < a.len() && a[i] == elem,
        decreases a.len() - pos,
    {
        if a[pos] == elem {
            found_pos = pos;
            found = true;
        }
        pos = pos + 1;
    }
    
    proof {
        assert(found);
        assert(a[found_pos as int] == elem);
        assert(forall|i: int| found_pos < i < a.len() ==> a[i] != elem);
    }
    
    found_pos
}
// </vc-code>

}
fn main() {}