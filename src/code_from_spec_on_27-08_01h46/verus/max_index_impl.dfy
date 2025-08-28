use vstd::prelude::*;

verus! {

// <vc-helpers>
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
    let mut max_index = 0;
    let mut i = 1;
    
    while i < x.len()
        invariant
            max_index < x.len(),
            i <= x.len(),
            forall|k: int| 0 <= k < i ==> x[max_index as int] >= x[k],
        decreases x.len() - i
    {
        if x[i] > x[max_index] {
            max_index = i;
        }
        i += 1;
    }
    
    max_index
}
// </vc-code>

} // verus!

fn main() {}