use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
fn myfun1(x: &Vec<i32>) -> (max_index: usize)
    // pre-conditions-start
    requires
        x.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|k: int| 0 <= k < x.len() ==> x[max_index as int] >= x[k],
        max_index < x.len(),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut max_idx: usize = 0;
    let mut i: usize = 1;
    
    while i < x.len()
        invariant
            0 <= max_idx < x.len(),
            0 <= i <= x.len(),
            forall|k: int| 0 <= k < i as int ==> x[max_idx as int] >= x[k],
        decreases x.len() - i
    {
        if x[i] > x[max_idx] {
            max_idx = i;
        }
        i = i + 1;
    }
    
    max_idx
}
// </vc-code>

} // verus!

fn main() {}