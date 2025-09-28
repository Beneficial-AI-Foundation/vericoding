use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn is_greater(n: i32, a: &[i32]) -> (result: bool)
    ensures 
        result ==> forall|i: int| 0 <= i < a.len() ==> n > a[i],
        !result ==> exists|i: int| 0 <= i < a.len() && n <= a[i],
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> n > a[j],
        decreases a.len() - i,
    {
        if n <= a[i] {
            // Found an element that is >= n
            assert(0 <= i < a.len() && n <= a[i as int]);
            assert(exists|k: int| 0 <= k < a.len() && n <= a[k]);
            return false;
        }
        i = i + 1;
    }
    
    // If we've checked all elements and none were >= n, then n is greater than all
    assert(i == a.len());
    assert(forall|j: int| 0 <= j < a.len() ==> n > a[j]);
    true
}
// </vc-code>

fn main() {
}

}