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
            forall|j: int| 0 <= j < i ==> 
                a.spec_index(j) <= a.spec_index(2*j + 1) && 
                (2*j + 2 >= a.len() || a.spec_index(j) <= a.spec_index(2*j + 2))
    {
        let left_child = 2 * i + 1;
        let right_child = 2 * i + 2;
        
        // Check left child
        if left_child < a.len() && a[i] > a[left_child] {
            assert(a.spec_index(i as int) > a.spec_index(2*(i as int) + 1));
            return false;
        }
        
        // Check right child if it exists
        if right_child < a.len() && a[i] > a[right_child] {
            assert(2*(i as int) + 2 < a.len() && a.spec_index(i as int) > a.spec_index(2*(i as int) + 2));
            return false;
        }
        
        i += 1;
    }
    
    // At this point, we've checked all internal nodes and they satisfy min-heap property
    assert(forall|j: int| 0 <= j < a.len() / 2 ==> 
        a.spec_index(j) <= a.spec_index(2*j + 1) && 
        (2*j + 2 >= a.len() || a.spec_index(j) <= a.spec_index(2*j + 2)));
    
    true
}

}