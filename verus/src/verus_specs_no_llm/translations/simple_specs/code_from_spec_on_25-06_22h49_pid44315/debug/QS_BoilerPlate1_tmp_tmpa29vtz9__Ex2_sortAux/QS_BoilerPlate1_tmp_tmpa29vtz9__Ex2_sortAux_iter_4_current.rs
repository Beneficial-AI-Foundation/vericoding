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
        result.push(a[i]);
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
}

// Helper lemma for merging sorted sequences
proof fn lemma_merge_maintains_sorted(a: Seq<int>, left: Seq<int>, right: Seq<int>, 
                                     l: int, m: int, r: int, merge_idx: int)
    requires
        sorted(left),
        sorted(right),
        0 <= l < m < r,
        l <= merge_idx <= r,
        forall|i: int| 0 <= i < left.len() ==> left[i] == a[l + i],
        forall|i: int| 0 <= i < right.len() ==> right[i] == a[m + i],
    ensures
        true, // Placeholder - helps with proof context
{
}

// Merge two sorted portions of an array
fn mergeArr(a: &mut Vec<int>, l: int, m: int, r: int)
    requires 
        0 <= l < m < r <= old(a).len(),
        sorted(old(a).subrange(l, m)),
        sorted(old(a).subrange(m, r)),
    ensures
        a.len() == old(a).len(),
        sorted(a.subrange(l, r)),
        a.subrange(0, l) =~= old(a).subrange(0, l),
        a.subrange(r, a.len() as int) =~= old(a).subrange(r, old(a).len() as int),
{
    // Create copies of the two sorted subarrays
    let left = copyArr(a.clone(), l, m);
    let right = copyArr(a.clone(), m, r);
    
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
            forall|x: int, y: int| l <= x < y < k ==> a[x] <= a[y],
            // Preserve parts outside [l,r)
            a.subrange(0, l) =~= old(a).subrange(0, l),
            a.subrange(r, a.len() as int) =~= old(a).subrange(r, old(a).len() as int),
            // Connection between original arrays and copies
            forall|idx: int| 0 <= idx < left.len() ==> left[idx] == old(a)[l + idx],
            forall|idx: int| 0 <= idx < right.len() ==> right[idx] == old(a)[m + idx],
    {
        if left[i] <= right[j] {
            // Prove that placing left[i] maintains sortedness
            if k > l {
                assert(forall|x: int| l <= x < k ==> a[x] <= left[i]) by {
                    // By loop invariant and sorted property of left array
                }
            }
            a.set(k, left[i]);
            i = i + 1;
        } else {
            // Prove that placing right[j] maintains sortedness
            if k > l {
                assert(forall|x: int| l <= x < k ==> a[x] <= right[j]) by {
                    // By loop invariant and sorted property of right array
                }
            }
            a.set(k, right[j]);
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
            forall|x: int, y: int| l <= x < y < k ==> a[x] <= a[y],
            // Preserve parts outside [l,r)
            a.subrange(0, l) =~= old(a).subrange(0, l),
            a.subrange(r, a.len() as int) =~= old(a).subrange(r, old(a).len() as int),
            // Connection between original arrays and copies
            forall|idx: int| 0 <= idx < left.len() ==> left[idx] == old(a)[l + idx],
    {
        // Prove sortedness is maintained
        if k > l {
            assert(a[k-1] <= left[i]) by {
                // By sorted property of left array and previous elements
            }
        }
        a.set(k, left[i]);
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
            forall|x: int, y: int| l <= x < y < k ==> a[x] <= a[y],
            // Preserve parts outside [l,r)
            a.subrange(0, l) =~= old(a).subrange(0, l),
            a.subrange(r, a.len() as int) =~= old(a).subrange(r, old(a).len() as int),
            // Connection between original arrays and copies
            forall|idx: int| 0 <= idx < right.len() ==> right[idx] == old(a)[m + idx],
    {
        // Prove sortedness is maintained
        if k > l {
            assert(a[k-1] <= right[j]) by {
                // By sorted property of right array and previous elements
            }
        }
        a.set(k, right[j]);
        j = j + 1;
        k = k + 1;
    }
    
    // Final assertions to help verification
    assert(k == r);
    assert(i == left.len());
    assert(j == right.len());
    
    // The sortedness of the final merged array follows from the loop invariants
    assert(sorted(a.subrange(l, r))) by {
        // This follows from the maintained invariant that elements are sorted
        assert(forall|x: int, y: int| l <= x < y < r ==> a[x] <= a[y]);
    }
}

// Recursive merge sort helper
fn sortAux(a: &mut Vec<int>, l: int, r: int)
    requires
        0 <= l <= r <= old(a).len(),
    ensures
        a.len() == old(a).len(),
        sorted(a.subrange(l, r)),
        a.subrange(0, l) =~= old(a).subrange(0, l),
        a.subrange(r, a.len() as int) =~= old(a).subrange(r, old(a).len() as int),
    decreases r - l,
{
    if r - l <= 1 {
        // Base case: array of size 0 or 1 is already sorted
        assert(sorted(a.subrange(l, r))) by {
            if r - l == 0 {
                // Empty sequence is sorted
                assert(a.subrange(l, r).len() == 0);
            } else {
                // Single element sequence is sorted
                assert(a.subrange(l, r).len() == 1);
                assert(forall|i: int, j: int| 0 <= i <= j < 1 ==> a.subrange(l, r)[i] <= a.subrange(l, r)[j]);
            }
        }
        return;
    }
    
    let m = l + (r - l) / 2;
    assert(l < m < r) by {
        assert(r - l > 1);
        assert((r - l) / 2 > 0);
        assert(m == l + (r - l) / 2);
        assert(m > l);
        assert(m < r);
    }
    
    // Sort first half
    sortAux(a, l, m);
    assert(sorted(a.subrange(l, m)));
    
    // Sort second half  
    sortAux(a, m, r);
    assert(sorted(a.subrange(m, r)));
    
    // Merge the sorted halves
    mergeArr(a, l, m, r);
    assert(sorted(a.subrange(l, r)));
}

}