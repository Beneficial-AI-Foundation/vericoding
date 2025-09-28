use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn update_elements(a: &mut Vec<i32>)
    requires 
        old(a).len() >= 8,
    ensures 
        old(a)[4] + 3 == a[4],
        a[7] == 516,
        forall|i: int| 0 <= i < a.len() ==> i != 7 && i != 4 ==> a[i] == old(a)[i],
        a.len() == old(a).len(),
// </vc-spec>
// <vc-code>
{
    proof {
        assert(old(a).len() >= 8);
        assert(a.len() == old(a).len());
    }
    
    // Ensure no overflow when adding 3 to a[4]
    assert(a[4] <= i32::MAX - 3);
    a[4] = a[4] + 3;
    a[7] = 516;
    
    proof {
        assert(a.len() == old(a).len());
        assert(forall|i: int| 0 <= i < a.len() && i != 7 && i != 4 ==> a[i] == old(a)[i]);
    }
}
// </vc-code>

fn main() {}

}