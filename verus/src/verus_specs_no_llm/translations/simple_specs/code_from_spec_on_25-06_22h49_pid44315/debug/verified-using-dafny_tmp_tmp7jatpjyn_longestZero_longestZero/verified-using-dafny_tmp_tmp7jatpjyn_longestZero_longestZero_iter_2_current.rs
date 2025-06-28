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
    let mut max_size = 0;
    let mut max_pos = 0;
    let mut current_size = 0;
    let mut current_start = 0;
    
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            0 <= max_size <= a.len(),
            0 <= max_pos <= a.len(),
            max_pos + max_size <= a.len(),
            0 <= current_size <= idx,
            0 <= current_start <= idx,
            current_start + current_size <= a.len(),
            // max_size represents the longest zero sequence found so far
            max_size == 0 || forall|i:int| max_pos <= i < max_pos + max_size ==> a.spec_index(i) == 0,
            // current_size represents current consecutive zeros ending at idx-1
            current_size == 0 || (current_start + current_size == idx && 
                forall|i:int| current_start <= i < current_start + current_size ==> a.spec_index(i) == 0),
            // No longer sequence exists before idx
            forall|i:int, j:int| (0 <= i <= j < idx && getSize(i, j) > max_size) ==> 
                exists|k:int| i <= k <= j && a.spec_index(k) != 0,
    {
        if a[idx] == 0 {
            if current_size == 0 {
                current_start = idx;
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
    
    // Handle case where no zeros found
    if max_size == 0 {
        // Find first non-zero position
        let mut pos = 0;
        while pos < a.len() && a[pos] == 0
            invariant
                0 <= pos <= a.len(),
                forall|i:int| 0 <= i < pos ==> a.spec_index(i) == 0,
        {
            pos += 1;
        }
        
        if pos == a.len() {
            // All elements are zero
            (a.len() as int, 0)
        } else {
            // Found non-zero element at pos, return zero-length sequence
            (0, pos)
        }
    } else {
        // Prove the final result satisfies the postcondition
        assert(max_size > 0);
        assert(0 <= max_pos <= a.len());
        assert(max_pos + max_size <= a.len());
        assert(forall|i:int| max_pos <= i < max_pos + max_size ==> a.spec_index(i) == 0);
        
        // Prove max_pos < a.len() when max_size > 0
        if max_size > 0 {
            assert(max_pos + max_size <= a.len());
            assert(max_pos < max_pos + max_size);
            assert(max_pos + max_size <= a.len());
            assert(max_pos < a.len());
        }
        
        (max_size, max_pos)
    }
}

}