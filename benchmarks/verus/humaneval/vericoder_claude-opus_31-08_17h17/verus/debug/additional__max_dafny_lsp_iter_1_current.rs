use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn max_dafny_lsp(a: &[i32]) -> (x: usize)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= x < a.len(),
        forall|k: int| 0 <= k < a.len() ==> a[k] <= a[x as int],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            0 <= max_idx < i,
            i <= a.len(),
            forall|k: int| 0 <= k < i ==> a[k] <= a[max_idx as int],
    {
        if a[i] > a[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    
    max_idx
}
// </vc-code>

fn main() {}
}