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
                assert(0 <= i as int < a.len() / 2);
                assert(left_child as int == 2 * (i as int) + 1);
                assert(a.spec_index(i as int) > a.spec_index(left_child as int));
                return false;
            }
        }
        
        // Check right child if it exists
        if right_child < a.len() {
            if a[i] > a[right_child] {
                // Provide witness for the negative postcondition
                assert(0 <= i as int < a.len() / 2);
                assert(right_child as int == 2 * (i as int) + 2);
                assert(right_child < a.len());
                assert(a.spec_index(i as int) > a.spec_index(right_child as int));
                return false;
            }
        }
        
        // Help prove the invariant is maintained
        assert(forall|j: int| 0 <= j < i + 1 ==> 
            a.spec_index(j) <= a.spec_index(2*j + 1) && 
            (2*j + 2 >= a.len() || a.spec_index(j) <= a.spec_index(2*j + 2))) by {
            assert(forall|j: int| 0 <= j < i ==> 
                a.spec_index(j) <= a.spec_index(2*j + 1) && 
                (2*j + 2 >= a.len() || a.spec_index(j) <= a.spec_index(2*j + 2)));
            
            // For j == i, we just verified the heap property
            if left_child < a.len() {
                assert(a.spec_index(i as int) <= a.spec_index(left_child as int));
                assert(left_child as int == 2 * (i as int) + 1);
            }
            if right_child < a.len() {
                assert(a.spec_index(i as int) <= a.spec_index(right_child as int));
                assert(right_child as int == 2 * (i as int) + 2);
            } else {
                assert(2 * (i as int) + 2 >= a.len());
            }
        };
        
        i += 1;
    }
    
    // At this point, we've verified all internal nodes satisfy the min-heap property
    assert(i as int == a.len() / 2);
    assert(forall|j: int| 0 <= j < a.len() / 2 ==> 
        a.spec_index(j) <= a.spec_index(2*j + 1) && 
        (2*j + 2 >= a.len() || a.spec_index(j) <= a.spec_index(2*j + 2)));
    
    true
}

}