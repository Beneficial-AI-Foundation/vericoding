use builtin::*;
use builtin_macros::*;

verus! {

// Define the sorted predicate
spec fn sorted(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i <= j < s.len() ==> s[i] <= s[j]
}

fn main() {
}

// Copy a portion of array from index l to r-1
fn copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>)
    requires 
        0 <= l <= r <= a.len(),
    ensures
        ret.len() == r - l,
        forall|k: int| 0 <= k < ret.len() ==> ret[k] == a[l + k],
{
    let mut result = Vec::new();
    let mut i = l;
    
    while i < r 
        invariant
            l <= i <= r,
            result.len() == i - l,
            forall|k: int| 0 <= k < result.len() ==> result[k] == a[l + k],
    {
        result.push(a[(l + (i - l)) as usize]);
        i = i + 1;
    }
    
    result
}

// Helper lemma to prove transitivity in sorted sequences
proof fn lemma_sorted_transitivity(s: Seq<int>, i: int, j: int, k: int)
    requires
        sorted(s),
        0 <= i <= j <= k < s.len(),
    ensures
        s[i] <= s[k],
{
    // This follows directly from the definition of sorted
}

// Helper lemma for sorted subsequences
proof fn lemma_sorted_subrange(s: Seq<int>, start: int, end: int)
    requires
        sorted(s),
        0 <= start <= end <= s.len(),
    ensures
        sorted(s.subrange(start, end)),
{
    let sub = s.subrange(start, end);
    assert forall|i: int, j: int| 0 <= i <= j < sub.len() implies sub[i] <= sub[j] by {
        assert(sub[i] == s[start + i]);
        assert(sub[j] == s[start + j]);
        assert(0 <= start + i <= start + j < s.len());
    }
}

// Merge two sorted portions of an array
fn mergeArr(a: &mut Vec<int>, l: int, m: int, r: int)
    requires 
        0 <= l < m < r <= old(a).len(),
        sorted(old(a)@.subrange(l, m)),
        sorted(old(a)@.subrange(m, r)),
    ensures
        a.len() == old(a).len(),
        sorted(a@.subrange(l, r)),
        a@.subrange(0, l) =~= old(a)@.subrange(0, l),
        a@.subrange(r, a.len() as int) =~= old(a)@.subrange(r, old(a).len() as int),
{
    // Create copies of the two sorted subarrays
    let left = copyArr((*a).clone(), l, m);
    let right = copyArr((*a).clone(), m, r);
    
    // Establish that the copies are sorted
    proof {
        lemma_sorted_subrange(old(a)@, l, m);
        lemma_sorted_subrange(old(a)@, m, r);
        
        // Prove left array is sorted
        assert forall|i: int, j: int| 0 <= i <= j < left.len() implies left@[i] <= left@[j] by {
            assert(left@[i] == old(a)@[l + i]);
            assert(left@[j] == old(a)@[l + j]);
            assert(l + i <= l + j < m <= old(a)@.len());
        }
        
        // Prove right array is sorted
        assert forall|i: int, j: int| 0 <= i <= j < right.len() implies right@[i] <= right@[j] by {
            assert(right@[i] == old(a)@[m + i]);
            assert(right@[j] == old(a)@[m + j]);
            assert(m + i <= m + j < r <= old(a)@.len());
        }
    }
    
    let mut i = 0int;  // Index for left array
    let mut j = 0int;  // Index for right array  
    let mut k = l;     // Index for merged array
    
    // Merge the two arrays
    while i < left.len() && j < right.len()
        invariant
            0 <= i <= left.len(),
            0 <= j <= right.len(),
            l <= k <= r,
            k == l + i + j,
            a.len() == old(a).len(),
            left.len() == m - l,
            right.len() == r - m,
            sorted(left@),
            sorted(right@),
            // Elements in merged portion are sorted
            forall|x: int, y: int| l <= x < y < k ==> a@[x] <= a@[y],
            // Preserve parts outside [l,r)
            a@.subrange(0, l) =~= old(a)@.subrange(0, l),
            a@.subrange(r, a.len() as int) =~= old(a)@.subrange(r, old(a).len() as int),
            // Connection between original arrays and copies
            forall|idx: int| 0 <= idx < left.len() ==> left@[idx] == old(a)@[l + idx],
            forall|idx: int| 0 <= idx < right.len() ==> right@[idx] == old(a)@[m + idx],
    {
        if left@[i] <= right@[j] {
            a.set(k as usize, left@[i]);
            i = i + 1;
        } else {
            a.set(k as usize, right@[j]);
            j = j + 1;
        }
        k = k + 1;
    }
    
    // Copy remaining elements from left array
    while i < left.len()
        invariant
            0 <= i <= left.len(),
            j == right.len(),
            l <= k <= r,
            k == l + i + right.len(),
            a.len() == old(a).len(),
            left.len() == m - l,
            right.len() == r - m,
            sorted(left@),
            // Elements in merged portion are sorted
            forall|x: int, y: int| l <= x < y < k ==> a@[x] <= a@[y],
            // Preserve parts outside [l,r)
            a@.subrange(0, l) =~= old(a)@.subrange(0, l),
            a@.subrange(r, a.len() as int) =~= old(a)@.subrange(r, old(a).len() as int),
            // Connection between original arrays and copies
            forall|idx: int| 0 <= idx < left.len() ==> left@[idx] == old(a)@[l + idx],
    {
        a.set(k as usize, left@[i]);
        i = i + 1;
        k = k + 1;
    }
    
    // Copy remaining elements from right array
    while j < right.len()
        invariant
            i == left.len(),
            0 <= j <= right.len(),
            l <= k <= r,
            k == l + left.len() + j,
            a.len() == old(a).len(),
            left.len() == m - l,
            right.len() == r - m,
            sorted(right@),
            // Elements in merged portion are sorted
            forall|x: int, y: int| l <= x < y < k ==> a@[x] <= a@[y],
            // Preserve parts outside [l,r)
            a@.subrange(0, l) =~= old(a)@.subrange(0, l),
            a@.subrange(r, a.len() as int) =~= old(a)@.subrange(r, old(a).len() as int),
            // Connection between original arrays and copies
            forall|idx: int| 0 <= idx < right.len() ==> right@[idx] == old(a)@[m + idx],
    {
        a.set(k as usize, right@[j]);
        j = j + 1;
        k = k + 1;
    }
    
    // Final proof that the merged range is sorted
    proof {
        assert(k == r);
        assert(i == left.len());
        assert(j == right.len());
        
        assert forall|x: int, y: int| l <= x <= y < r implies a@[x] <= a@[y] by {
            // The sortedness follows from the loop invariants maintained above
        }
    }
}

// Recursive merge sort helper
fn sortAux(a: &mut Vec<int>, l: int, r: int)
    requires
        0 <= l <= r <= old(a).len(),
    ensures
        a.len() == old(a).len(),
        sorted(a@.subrange(l, r)),
        a@.subrange(0, l) =~= old(a)@.subrange(0, l),
        a@.subrange(r, a.len() as int) =~= old(a)@.subrange(r, old(a).len() as int),
    decreases r - l,
{
    if r - l <= 1 {
        // Base case: array of size 0 or 1 is already sorted
        proof {
            let sub = a@.subrange(l, r);
            assert forall|i: int, j: int| 0 <= i <= j < sub.len() implies sub[i] <= sub[j] by {
                // Trivially true for sequences of length <= 1
                assert(sub.len() <= 1);
            }
        }
        return;
    }
    
    let m = l + (r - l) / 2;
    
    // Sort first half
    sortAux(a, l, m);
    
    // Sort second half  
    sortAux(a, m, r);
    
    // Merge the sorted halves
    mergeArr(a, l, m, r);
}

}