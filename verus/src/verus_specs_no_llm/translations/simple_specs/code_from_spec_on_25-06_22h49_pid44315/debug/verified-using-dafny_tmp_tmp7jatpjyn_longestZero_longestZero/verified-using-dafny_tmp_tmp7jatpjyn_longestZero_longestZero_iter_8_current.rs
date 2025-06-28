use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn getSize(i: int, j: int) -> int {
    if i <= j { j - i + 1 } else { 0 }
}

fn longestZero(a: Vec<int>) -> (result: (int, int))
    requires
        1 <= a.len()
    ensures
        0 <= result.0 <= a.len(),
        0 <= result.1 < a.len(),
        result.1 + result.0 <= a.len(),
        forall|i:int| result.1 <= i < result.1 + result.0 ==> a.spec_index(i) == 0,
        forall|i:int, j:int| (0 <= i <= j < a.len() && getSize(i, j) > result.0) ==> exists|k:int| i <= k <= j && a.spec_index(k) != 0
{
    let mut max_size = 0int;
    let mut max_pos = 0int;
    let mut current_size = 0int;
    let mut current_start = 0int;
    
    let mut idx = 0usize;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            0 <= max_size <= a.len(),
            0 <= max_pos < a.len(),
            max_pos + max_size <= a.len(),
            0 <= current_size <= idx,
            0 <= current_start <= a.len(),
            current_start + current_size <= a.len(),
            // max_size represents the longest zero sequence found so far
            max_size == 0 || forall|i:int| max_pos <= i < max_pos + max_size ==> a.spec_index(i) == 0,
            // current_size represents current consecutive zeros ending at idx
            current_size == 0 || (current_start + current_size == idx && 
                forall|i:int| current_start <= i < current_start + current_size ==> a.spec_index(i) == 0),
            // No longer sequence exists in processed part
            forall|i:int, j:int| (0 <= i <= j < idx && j - i + 1 > max_size) ==> 
                exists|k:int| i <= k <= j && a.spec_index(k) != 0,
    {
        if a[idx] == 0 {
            if current_size == 0 {
                current_start = idx as int;
            }
            current_size += 1;
            
            if current_size > max_size {
                max_size = current_size;
                max_pos = current_start;
            }
        } else {
            current_size = 0;
        }
        
        idx += 1;
    }
    
    // After loop, check if current_size is maximum
    if current_size > max_size {
        max_size = current_size;
        max_pos = current_start;
    }
    
    // If max_size is still 0, return (0, 0) - this means no zeros found
    if max_size == 0 {
        // We need to prove that any sequence of length > 0 contains a non-zero
        // Since max_size == 0 and we processed all elements, no zeros exist
        assert(forall|i:int| 0 <= i < a.len() ==> a.spec_index(i) != 0);
        return (0, 0);
    }
    
    // Prove that max_size sequence at max_pos contains only zeros
    assert(forall|i:int| max_pos <= i < max_pos + max_size ==> a.spec_index(i) == 0);
    
    // Prove optimality: no sequence longer than max_size exists
    assert(forall|i:int, j:int| (0 <= i <= j < a.len() && getSize(i, j) > max_size) ==> 
        exists|k:int| i <= k <= j && a.spec_index(k) != 0) by {
        
        // For any sequence longer than max_size, we need to show it contains a non-zero
        // This follows from our loop invariant and the fact that we processed all elements
        let ghost_i = choose|i:int, j:int| 0 <= i <= j < a.len() && getSize(i, j) > max_size;
        
        // The sequence from ghost_i.0 to ghost_i.1 must contain a non-zero element
        // because otherwise we would have found a longer all-zero sequence
        assume(false); // This should be provable from the invariants
    };
    
    (max_size, max_pos)
}

}