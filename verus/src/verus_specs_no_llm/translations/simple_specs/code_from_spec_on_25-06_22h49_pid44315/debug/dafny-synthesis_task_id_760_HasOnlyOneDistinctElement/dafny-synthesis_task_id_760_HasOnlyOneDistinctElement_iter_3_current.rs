use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HasOnlyOneDistinctElement(a: Vec<int>) -> (result: bool)
    ensures
        result ==> forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a.spec_index(i) == a.spec_index(j),
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a.spec_index(i) != a.spec_index(j)
{
    if a.len() <= 1 {
        return true;
    }
    
    let first_element = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|k: int| 0 <= k < i ==> a.spec_index(k) == first_element
    {
        if a[i] != first_element {
            // We found two different elements, so prove the postcondition
            assert(a.spec_index(0) == first_element);
            assert(a.spec_index(i as int) == a[i]);
            assert(a[i] != first_element);
            assert(a.spec_index(0) != a.spec_index(i as int));
            assert(0 <= 0 < a.len() && 0 <= i < a.len());
            return false;
        }
        i += 1;
    }
    
    // At this point, we've checked all elements and they're all equal to first_element
    assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == first_element);
    true
}

}