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
        result.push(a[i as usize]);
        i = i + 1;
    }
    
    result
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
            // Preserve parts outside [l,r)
            a.subrange(0, l) =~= old(a).subrange(0, l),
            a.subrange(r, a.len() as int) =~= old(a).subrange(r, old(a).len() as int),
    {
        if left[i as usize] <= right[j as usize] {
            a.set(k as usize, left[i as usize]);
            i = i + 1;
        } else {
            a.set(k as usize, right[j as usize]);
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
            k == l + i + j,
            a.len() == old(a).len(),
            a.subrange(0, l) =~= old(a).subrange(0, l),
            a.subrange(r, a.len() as int) =~= old(a).subrange(r, old(a).len() as int),
    {
        a.set(k as usize, left[i as usize]);
        i = i + 1;
        k = k + 1;
    }
    
    // Copy remaining elements from right array
    while j < right.len()
        invariant
            i == left.len(),
            0 <= j <= right.len(),
            l <= k <= r,
            k == l + i + j,
            a.len() == old(a).len(),
            a.subrange(0, l) =~= old(a).subrange(0, l),
            a.subrange(r, a.len() as int) =~= old(a).subrange(r, old(a).len() as int),
    {
        a.set(k as usize, right[j as usize]);
        j = j + 1;
        k = k + 1;
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