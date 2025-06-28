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
                assert(i < half_len);
                assert(half_len == a.len() / 2);
                assert((i as int) < (a.len() / 2) as int);
                return false;
            }
        }
        
        // Check right child if it exists
        if right_child < a.len() {
            if a[i] > a[right_child] {
                // Provide witness for the negative postcondition
                assert(i < half_len);
                assert(half_len == a.len() / 2);
                assert((i as int) < (a.len() / 2) as int);
                return false;
            }
        }
        
        i += 1;
    }
    
    true
}

}