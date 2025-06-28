use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsMinHeap(a: Vec<int>) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a.len() / 2 ==> 
            a.spec_index(i) <= a.spec_index(2*i + 1) && 
            (2*i + 2 >= a.len() || a.spec_index(i) <= a.spec_index(2*i + 2)),
        !result ==> exists|i: int| 0 <= i < a.len() / 2 && 
            (a.spec_index(i) > a.spec_index(2*i + 1) || 
             (2*i + 2 < a.len() && a.spec_index(i) > a.spec_index(2*i + 2)))
{
    if a.len() == 0 {
        return true;
    }
    
    let mut i: usize = 0;
    let half_len = a.len() / 2;
    
    while i < half_len
        invariant
            0 <= i <= half_len,
            half_len == a.len() / 2,
            forall|j: int| 0 <= j < i ==> 
                a.spec_index(j) <= a.spec_index(2*j + 1) && 
                (2*j + 2 >= a.len() || a.spec_index(j) <= a.spec_index(2*j + 2))
    {
        let left_child = 2 * i + 1;
        let right_child = 2 * i + 2;
        
        // Check left child
        if left_child < a.len() {
            if a[i] > a[left_child] {
                // Provide witness for the negative postcondition
                assert(0 <= i < half_len);
                assert(half_len <= a.len() / 2);
                assert(0 <= i as int < a.len() / 2);
                assert((left_child as int) == 2 * (i as int) + 1);
                assert(a.spec_index(i as int) > a.spec_index(left_child as int));
                return false;
            }
        }
        
        // Check right child if it exists
        if right_child < a.len() {
            if a[i] > a[right_child] {
                // Provide witness for the negative postcondition
                assert(0 <= i < half_len);
                assert(half_len <= a.len() / 2);
                assert(0 <= i as int < a.len() / 2);
                assert((right_child as int) == 2 * (i as int) + 2);
                assert((right_child as int) < a.len());
                assert(a.spec_index(i as int) > a.spec_index(right_child as int));
                return false;
            }
        }
        
        // Help prove the invariant is maintained
        assert(forall|j: int| 0 <= j < (i + 1) as int ==> 
            a.spec_index(j) <= a.spec_index(2*j + 1) && 
            (2*j + 2 >= a.len() || a.spec_index(j) <= a.spec_index(2*j + 2))) by {
            
            // The invariant holds for all j < i by the loop invariant
            assert(forall|j: int| 0 <= j < i as int ==> 
                a.spec_index(j) <= a.spec_index(2*j + 1) && 
                (2*j + 2 >= a.len() || a.spec_index(j) <= a.spec_index(2*j + 2)));
            
            // For j == i, we just verified the heap property
            let j = i as int;
            assert(j == i as int);
            
            // Left child check
            assert(2*j + 1 == (left_child as int));
            if left_child < a.len() {
                assert(a[i] <= a[left_child]);
                assert(a.spec_index(j) <= a.spec_index(2*j + 1));
            }
            
            // Right child check
            assert(2*j + 2 == (right_child as int));
            if right_child < a.len() {
                assert(a[i] <= a[right_child]);
                assert(a.spec_index(j) <= a.spec_index(2*j + 2));
            } else {
                assert(2*j + 2 >= a.len());
            }
        }
        
        i += 1;
    }
    
    // At this point, we've verified all internal nodes satisfy the min-heap property
    assert(i == half_len);
    assert(half_len == a.len() / 2);
    assert(forall|j: int| 0 <= j < a.len() / 2 ==> 
        a.spec_index(j) <= a.spec_index(2*j + 1) && 
        (2*j + 2 >= a.len() || a.spec_index(j) <= a.spec_index(2*j + 2)));
    
    true
}

}