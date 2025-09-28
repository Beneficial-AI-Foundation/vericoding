use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn all_elements_equal(a: &[i32], n: i32) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() ==> a[i] == n,
        !result ==> exists|i: int| 0 <= i < a.len() && a[i] != n,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a[j] == n,
        decreases a.len() - i,
    {
        if a[i] != n {
            // Found an element that doesn't equal n
            assert(a[i as int] != n);
            assert(0 <= i < a.len());
            return false;
        }
        i += 1;
    }
    
    // If we've checked all elements and none were different from n,
    // then all elements equal n
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> a[j] == n);
    true
}
// </vc-code>

fn main() {
}

}