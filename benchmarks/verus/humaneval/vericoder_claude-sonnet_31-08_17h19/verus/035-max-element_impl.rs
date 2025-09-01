use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn max_element(a: &Vec<i32>) -> (max: i32)
    // pre-conditions-start
    requires
        a.len() > 0,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| 0 <= i < a.len() ==> a[i] <= max,
        exists|i: int| 0 <= i < a.len() && a[i] == max,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut max = a[0];
    let mut i = 1;
    
    while i < a.len()
        invariant
            0 < i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] <= max,
            exists|j: int| 0 <= j < i && a[j] == max,
        decreases a.len() - i,
    {
        if a[i] > max {
            max = a[i];
        }
        i += 1;
    }
    
    max
    // impl-end
}
// </vc-code>

fn main() {}
}