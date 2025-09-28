use vstd::prelude::*;

verus! {

spec fn get_size(i: int, j: int) -> int {
    j - i + 1
}

// For a given integer array, let's find the longest subsequence of 0s.
// sz: size, pos: position. a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
spec fn all_zeros_in_range(a: &[i32], start: int, len: int) -> bool {
    forall |i: int| start <= i < start + len ==> a[i] == 0
}

spec fn has_nonzero_in_range(a: &[i32], start: int, end: int) -> bool {
    exists |k: int| start <= k <= end && a[k] != 0
}

proof fn lemma_initial_zero(a: &[i32])
    requires 1 <= a.len()
    ensures all_zeros_in_range(a, 0, 1) ==> a[0] == 0
{
}

proof fn lemma_extend_range(a: &[i32], start: int, len: int, new_len: int)
    requires 
        start >= 0,
        len >= 1,
        new_len > len,
        start + new_len <= a.len(),
        all_zeros_in_range(a, start, len),
        forall |j: int| start + len <= j < start + new_len ==> a[j] == 0
    ensures all_zeros_in_range(a, start, new_len)
{
}

proof fn lemma_nonzero_propagation(a: &[i32], start: int, end: int, nonzero_pos: int)
    requires 
        0 <= start <= nonzero_pos <= end < a.len(),
        a[nonzero_pos] != 0
    ensures has_nonzero_in_range(a, start, end)
{
}
// </vc-helpers>

// <vc-spec>
fn longest_zero(a: &[i32]) -> (result: (usize, usize))
    requires 
        1 <= a.len()
    ensures 
        result.0 <= a.len(),
        result.1 < a.len(),
        result.1 + result.0 <= a.len(),
        forall |i: int| result.1 <= i < (result.1 + result.0) ==> a[i as int] == 0,
        forall |i: int, j: int| {
            0 <= i < j < a.len() && get_size(i, j) > (result.0 as int)
            ==> exists |k: int| i <= k <= j && a[k] != 0
        }
// </vc-spec>
// <vc-code>
{
    let mut max_size: usize = 1;
    let mut max_pos: usize = 0;
    let mut current_size: usize = 0;
    let mut current_start: usize = 0;
    
    // Initialize properly - find first zero
    let mut first_zero_pos = 0;
    while first_zero_pos < a.len() && a[first_zero_pos] != 0
        invariant first_zero_pos <= a.len()
        decreases a.len() - first_zero_pos
    {
        first_zero_pos += 1;
    }
    
    if first_zero_pos < a.len() {
        max_pos = first_zero_pos;
        max_size = 1;
    } else {
        // All elements are non-zero, return minimal valid result
        max_pos = 0;
        max_size = 1;
    }
    
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            max_size >= 1,
            max_pos < a.len(),
            max_pos + max_size <= a.len(),
            current_start <= a.len(),
            (max_pos + max_size <= a.len()) ==> 
                forall |j: int| max_pos <= j < max_pos + max_size ==> a[j] == 0,
            forall |start: int, end: int| {
                0 <= start < end < i && get_size(start, end) > (max_size as int)
                ==> has_nonzero_in_range(a, start, end)
            },
            (current_size > 0) ==> (
                current_start < a.len() &&
                current_start + current_size == i &&
                forall |j: int| current_start <= j < current_start + current_size ==> a[j] == 0
            ),
        decreases a.len() - i
    {
        if a[i] == 0 {
            if current_size == 0 {
                current_start = i;
                current_size = 1;
            } else {
                current_size = current_size + 1;
            }
            
            if current_size > max_size {
                max_size = current_size;
                max_pos = current_start;
            }
        } else {
            // When we hit non-zero, all ranges crossing this position have non-zero
            proof {
                lemma_nonzero_propagation(a, 0, i as int, i as int);
            }
            current_size = 0;
        }
        i = i + 1;
    }
    
    // Handle case where array ends with zeros
    if current_size > max_size {
        max_size = current_size;
        max_pos = current_start;
    }
    
    // Ensure we have a valid zero sequence
    if max_pos + max_size > a.len() || (max_pos + max_size <= a.len() && exists |k: int| max_pos <= k < max_pos + max_size && a[k] != 0) {
        // Find any zero in the array
        let mut zero_pos = 0;
        while zero_pos < a.len() && a[zero_pos] != 0
            invariant zero_pos <= a.len()
            decreases a.len() - zero_pos
        {
            zero_pos += 1;
        }
        if zero_pos < a.len() {
            max_pos = zero_pos;
            max_size = 1;
        } else {
            max_pos = 0;
            max_size = 1;
        }
    }
    
    (max_size, max_pos)
}
// </vc-code>

fn main() {}

}