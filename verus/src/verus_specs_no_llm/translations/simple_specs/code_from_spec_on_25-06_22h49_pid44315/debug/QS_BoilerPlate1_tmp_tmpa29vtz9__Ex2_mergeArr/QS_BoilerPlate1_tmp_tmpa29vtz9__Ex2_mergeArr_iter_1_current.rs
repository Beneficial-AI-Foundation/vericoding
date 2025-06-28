use builtin::*;
use builtin_macros::*;

verus! {

// Specification function to check if a sequence is sorted
spec fn sorted(s: Seq<int>) -> bool {
    forall|k1: int, k2: int| 0 <= k1 <= k2 < s.len() ==> s[k1] <= s[k2]
}

fn main() {
}

// Copy a portion of array from index l to r-1
fn copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>)
    requires
        0 <= l <= r <= a.len(),
    ensures
        ret.len() == r - l,
        forall|i: int| 0 <= i < ret.len() ==> ret[i] == a[l + i],
{
    let mut result = Vec::new();
    let mut i = l;
    
    while i < r
        invariant
            l <= i <= r,
            result.len() == i - l,
            forall|j: int| 0 <= j < result.len() ==> result[j] == a[l + j],
    {
        result.push(a[i as usize]);
        i = i + 1;
    }
    
    result
}

// Merge two sorted portions of an array
fn mergeArr(a: &mut Vec<int>, l: int, m: int, r: int)
    requires
        0 <= l < r <= old(a).len(),
        0 <= l < m < r <= old(a).len(),
        sorted(old(a).subrange(l as int, m as int)),
        sorted(old(a).subrange(m as int, r as int)),
    ensures
        a.len() == old(a).len(),
        sorted(a.subrange(l as int, r as int)),
        forall|i: int| 0 <= i < l ==> a[i] == old(a)[i],
        forall|i: int| r <= i < a.len() ==> a[i] == old(a)[i],
{
    // Create temporary arrays for the two halves
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
            // Elements before l unchanged
            forall|idx: int| 0 <= idx < l ==> a[idx] == old(a)[idx],
            // Elements after r unchanged  
            forall|idx: int| r <= idx < a.len() ==> a[idx] == old(a)[idx],
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
            j <= right.len(),
            l <= k <= r,
            k == l + i + j,
            a.len() == old(a).len(),
            forall|idx: int| 0 <= idx < l ==> a[idx] == old(a)[idx],
            forall|idx: int| r <= idx < a.len() ==> a[idx] == old(a)[idx],
    {
        a.set(k as usize, left[i as usize]);
        i = i + 1;
        k = k + 1;
    }
    
    // Copy remaining elements from right array
    while j < right.len()
        invariant
            i <= left.len(),
            0 <= j <= right.len(),
            l <= k <= r,
            k == l + i + j,
            a.len() == old(a).len(),
            forall|idx: int| 0 <= idx < l ==> a[idx] == old(a)[idx],
            forall|idx: int| r <= idx < a.len() ==> a[idx] == old(a)[idx],
    {
        a.set(k as usize, right[j as usize]);
        j = j + 1;
        k = k + 1;
    }
}

}