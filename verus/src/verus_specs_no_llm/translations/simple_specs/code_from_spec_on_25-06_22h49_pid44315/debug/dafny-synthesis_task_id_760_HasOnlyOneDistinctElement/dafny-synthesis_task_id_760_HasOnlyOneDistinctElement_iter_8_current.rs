use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn HasOnlyOneDistinctElement(a: Vec<int>) -> (result: bool)
    ensures
        result ==> (a.len() == 0 || forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> a.spec_index(i) == a.spec_index(j)),
        !result ==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a.spec_index(i) != a.spec_index(j)
{
    if a.len() == 0 {
        return true;
    }
    
    if a.len() == 1 {
        return true;
    }
    
    let first_element = a[0];
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            first_element == a.spec_index(0),
            forall|k: int| 0 <= k < i ==> a.spec_index(k) == a.spec_index(0)
    {
        if a[i] != first_element {
            // We found two different elements
            assert(a.spec_index(0) != a.spec_index(i as int));
            return false;
        }
        
        i += 1;
    }
    
    // All elements are equal to the first element
    assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == a.spec_index(0));
    
    // Prove that all pairs of elements are equal
    assert(forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() ==> 
        a.spec_index(i) == a.spec_index(j)) by {
        // If both i and j are valid indices, they both equal a.spec_index(0)
        // Therefore they equal each other
        assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == a.spec_index(0));
    };
    
    true
}

}