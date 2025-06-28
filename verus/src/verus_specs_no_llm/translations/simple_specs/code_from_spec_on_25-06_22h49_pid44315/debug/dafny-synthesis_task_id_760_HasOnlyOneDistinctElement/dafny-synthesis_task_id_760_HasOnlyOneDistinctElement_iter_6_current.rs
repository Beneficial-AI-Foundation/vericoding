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
    let ghost first_elem_spec = a.spec_index(0);
    let mut i: usize = 1;
    
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            first_element == first_elem_spec,
            first_elem_spec == a.spec_index(0),
            forall|k: int| 0 <= k < i ==> a.spec_index(k) == first_elem_spec
    {
        if a[i] != first_element {
            // We found two different elements, so prove the postcondition
            assert(a.spec_index(0) == first_elem_spec);
            assert(a.spec_index(i as int) == a[i]);
            assert(a[i] != first_element);
            assert(first_element == first_elem_spec);
            assert(a.spec_index(0) != a.spec_index(i as int));
            assert(0 <= 0 < a.len() && 0 <= (i as int) < a.len());
            assert(exists|x: int, y: int| 0 <= x < a.len() && 0 <= y < a.len() && a.spec_index(x) != a.spec_index(y)) by {
                assert(a.spec_index(0) != a.spec_index(i as int));
            }
            return false;
        }
        
        // Prove the invariant for the next iteration
        assert(a[i] == first_element);
        assert(a.spec_index(i as int) == a[i]);
        assert(a.spec_index(i as int) == first_element);
        assert(a.spec_index(i as int) == first_elem_spec);
        
        i += 1;
    }
    
    // At this point, we've checked all elements and they're all equal to first_element
    assert(i == a.len());
    assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == first_elem_spec);
    assert(forall|x: int, y: int| 0 <= x < a.len() && 0 <= y < a.len() ==> 
        a.spec_index(x) == first_elem_spec && a.spec_index(y) == first_elem_spec) by {
        assert(forall|k: int| 0 <= k < a.len() ==> a.spec_index(k) == first_elem_spec);
    }
    assert(forall|x: int, y: int| 0 <= x < a.len() && 0 <= y < a.len() ==> 
        a.spec_index(x) == a.spec_index(y)) by {
        assert(forall|x: int, y: int| 0 <= x < a.len() && 0 <= y < a.len() ==> 
            a.spec_index(x) == first_elem_spec && a.spec_index(y) == first_elem_spec);
    }
    
    true
}

}