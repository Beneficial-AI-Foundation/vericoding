use vstd::prelude::*;

verus! {

spec fn get_size(i: int, j: int) -> int {
    j - i + 1
}

// For a given integer array, let's find the longest subsequence of 0s.
// sz: size, pos: position. a[pos..(pos+sz)] will be all zeros

// <vc-helpers>
// Helper lemma to prove that if we have a sequence of zeros from i to j,
// then all elements in that range are zero
proof fn zeros_in_range(a: &[i32], start: int, end: int)
    requires
        0 <= start <= end <= a.len(),
        forall |k: int| start <= k < end ==> a@[k] == 0,
    ensures
        forall |k: int| start <= k < end ==> a@[k] == 0,
{
}

// Helper lemma about subsequences containing non-zeros
proof fn subsequence_contains_nonzero(a: &[i32], i: int, j: int, witness: int)
    requires
        0 <= i <= witness <= j < a.len(),
        a@[witness] != 0,
    ensures
        exists |k: int| i <= k <= j && a@[k] != 0,
{
    assert(i <= witness <= j && a@[witness] != 0);
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
    let mut max_sz: usize = 0;
    let mut max_pos: usize = 0;
    let mut current_sz: usize = 0;
    let mut current_pos: usize = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            max_sz <= i,
            max_pos <= i,
            current_sz <= i,
            current_pos <= i,
            max_pos + max_sz <= i,
            current_pos + current_sz <= i,
            // max_sz and max_pos form a valid zero sequence or are both 0
            max_sz == 0 || (max_pos < a.len() && max_pos + max_sz <= a.len()),
            forall |k: int| max_pos as int <= k < (max_pos + max_sz) as int ==> a@[k] == 0,
            // current sequence is all zeros
            forall |k: int| current_pos as int <= k < (current_pos + current_sz) as int ==> a@[k] == 0,
            // max_sz is optimal up to position i
            forall |start: int, end: int| 
                0 <= start <= end && end <= i as int && get_size(start, end) > max_sz as int
                ==> exists |k: int| start <= k <= end && a@[k] != 0,
            // if we're in a sequence, it extends to i
            current_sz > 0 ==> current_pos + current_sz == i,
        decreases a.len() - i,
    {
        if a[i] == 0 {
            if current_sz == 0 {
                current_pos = i;
                current_sz = 1;
            } else {
                current_sz = current_sz + 1;
            }
            
            if current_sz > max_sz {
                max_sz = current_sz;
                max_pos = current_pos;
            }
        } else {
            // a[i] != 0, so any sequence crossing position i contains a non-zero
            proof {
                // For any sequence [start, end] where start <= i <= end < i+1
                // we know a[i] != 0, so the sequence contains a non-zero
                assert forall |start: int, end: int| 
                    0 <= start <= i as int && i as int <= end < (i + 1) as int
                    implies #[trigger] (exists |k: int| start <= k <= end && a@[k] != 0) by {
                    if 0 <= start <= i as int && i as int <= end < (i + 1) as int {
                        assert(a@[i as int] != 0);
                        subsequence_contains_nonzero(a, start, end, i as int);
                    }
                }
            }
            current_sz = 0;
        }
        
        i = i + 1;
    }
    
    // At this point, we've examined all positions
    assert(i == a.len());
    
    // The invariant tells us max_sz is optimal for all sequences ending at or before a.len()
    assert forall |start: int, end: int| 
        0 <= start <= end && end <= a.len() && get_size(start, end) > max_sz as int
        implies exists |k: int| start <= k <= end && a@[k] != 0;
    
    // Since get_size(i,j) = j - i + 1, for any 0 <= i < j < a.len(), we have end = j < a.len()
    // So the optimality condition is satisfied
    assert forall |i: int, j: int|
        0 <= i < j < a.len() && get_size(i, j) > max_sz as int
        implies #[trigger] (exists |k: int| i <= k <= j && a@[k] != 0) by {
        if 0 <= i < j < a.len() && get_size(i, j) > max_sz as int {
            // get_size(i, j) = j - i + 1, so we're looking at sequence from i to j
            assert(0 <= i <= j && j < a.len());
            assert(exists |k: int| i <= k <= j && a@[k] != 0);
        }
    }
    
    if max_sz == 0 {
        // No zeros found
        assert(forall |k: int| 0 <= k < a.len() ==> a@[k] != 0);
        (0, 0)
    } else {
        (max_sz, max_pos)
    }
}
// </vc-code>

fn main() {}

}