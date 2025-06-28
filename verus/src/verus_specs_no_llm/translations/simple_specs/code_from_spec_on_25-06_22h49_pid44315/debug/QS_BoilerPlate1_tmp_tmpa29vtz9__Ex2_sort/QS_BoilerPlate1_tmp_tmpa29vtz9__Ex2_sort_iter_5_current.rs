use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// ATOM - spec function for checking if a sequence is sorted
spec fn sorted(s: Seq<int>) -> bool {
    forall|k1: int, k2: int| 0 <= k1 <= k2 < s.len() ==> s[k1] <= s[k2]
}

// Helper spec function to check if one sequence is a merge of two sorted sequences
spec fn is_merge_of(result: Seq<int>, left: Seq<int>, right: Seq<int>) -> bool {
    result.to_multiset() == left.to_multiset().add(right.to_multiset())
}

// Helper spec function to check if a sequence is sorted up to a certain index
spec fn sorted_up_to(s: Seq<int>, start: int, end: int, current: int) -> bool {
    forall|k1: int, k2: int| start <= k1 <= k2 < current ==> s[k1] <= s[k2]
}

// Ex1 - Copy array function
fn copyArr(a: &Vec<int>, l: usize, r: usize) -> (ret: Vec<int>)
    requires 
        l < r,
        r <= a.len()
    ensures
        ret.len() == r - l,
        ret@ == a@.subrange(l as int, r as int)
{
    let mut result = Vec::new();
    let mut i = l;
    while i < r
        invariant
            l <= i <= r,
            result.len() == i - l,
            result@ == a@.subrange(l as int, i as int)
    {
        result.push(a[i]);
        i += 1;
    }
    result
}

// Ex2 - Merge function implementation
fn mergeArr(a: &mut Vec<int>, l: usize, m: usize, r: usize)
    requires 
        l < m < r,
        r <= old(a).len(),
        sorted(old(a)@.subrange(l as int, m as int)),
        sorted(old(a)@.subrange(m as int, r as int))
    ensures
        a.len() == old(a).len(),
        sorted(a@.subrange(l as int, r as int)),
        a@.subrange(0, l as int) == old(a)@.subrange(0, l as int),
        a@.subrange(r as int, a.len() as int) == old(a)@.subrange(r as int, old(a).len() as int),
        is_merge_of(a@.subrange(l as int, r as int), 
                   old(a)@.subrange(l as int, m as int), 
                   old(a)@.subrange(m as int, r as int))
{
    // Create temporary arrays for left and right subarrays
    let left = copyArr(a, l, m);
    let right = copyArr(a, m, r);
    
    let mut i = 0usize;  // Index for left array
    let mut j = 0usize;  // Index for right array
    let mut k = l;       // Index for merged array
    
    // Merge the two arrays
    while i < left.len() && j < right.len()
        invariant
            k == l + i + j,
            i <= left.len(),
            j <= right.len(),
            k <= r,
            left@ == old(a)@.subrange(l as int, m as int),
            right@ == old(a)@.subrange(m as int, r as int),
            a.len() == old(a).len(),
            // Preserve elements outside the range
            a@.subrange(0, l as int) == old(a)@.subrange(0, l as int),
            a@.subrange(r as int, a.len() as int) == old(a)@.subrange(r as int, old(a).len() as int),
            // Sortedness property for merged portion
            sorted(a@.subrange(l as int, k as int)),
            // Multiset property for elements placed so far
            a@.subrange(l as int, k as int).to_multiset() == 
                left@.subrange(0, i as int).to_multiset().add(right@.subrange(0, j as int).to_multiset()),
            // Ordering constraint between merged elements and remaining elements
            forall|idx: int| l <= idx < k && i < left.len() ==> a[idx] <= left[i as int],
            forall|idx: int| l <= idx < k && j < right.len() ==> a[idx] <= right[j as int]
    {
        if left[i] <= right[j] {
            a.set(k, left[i]);
            i += 1;
        } else {
            a.set(k, right[j]);
            j += 1;
        }
        k += 1;
    }
    
    // Copy remaining elements from left array
    while i < left.len()
        invariant
            j == right.len(),
            k == l + i + j,
            i <= left.len(),
            k <= r,
            left@ == old(a)@.subrange(l as int, m as int),
            right@ == old(a)@.subrange(m as int, r as int),
            a.len() == old(a).len(),
            a@.subrange(0, l as int) == old(a)@.subrange(0, l as int),
            a@.subrange(r as int, a.len() as int) == old(a)@.subrange(r as int, old(a).len() as int),
            sorted(a@.subrange(l as int, k as int)),
            a@.subrange(l as int, k as int).to_multiset() == 
                left@.subrange(0, i as int).to_multiset().add(right@.to_multiset()),
            forall|idx: int| l <= idx < k && i < left.len() ==> a[idx] <= left[i as int]
    {
        a.set(k, left[i]);
        i += 1;
        k += 1;
    }
    
    // Copy remaining elements from right array
    while j < right.len()
        invariant
            i == left.len(),
            k == l + i + j,
            j <= right.len(),
            k <= r,
            left@ == old(a)@.subrange(l as int, m as int),
            right@ == old(a)@.subrange(m as int, r as int),
            a.len() == old(a).len(),
            a@.subrange(0, l as int) == old(a)@.subrange(0, l as int),
            a@.subrange(r as int, a.len() as int) == old(a)@.subrange(r as int, old(a).len() as int),
            sorted(a@.subrange(l as int, k as int)),
            a@.subrange(l as int, k as int).to_multiset() == 
                left@.to_multiset().add(right@.subrange(0, j as int).to_multiset()),
            forall|idx: int| l <= idx < k && j < right.len() ==> a[idx] <= right[j as int]
    {
        a.set(k, right[j]);
        j += 1;
        k += 1;
    }
    
    // Add proof to help verify the multiset property
    proof {
        assert(k == r);
        assert(i == left.len());
        assert(j == right.len());
        
        // Help prove multiset equality
        let final_range = a@.subrange(l as int, r as int);
        let left_range = old(a)@.subrange(l as int, m as int);
        let right_range = old(a)@.subrange(m as int, r as int);
        
        assert(left@ == left_range);
        assert(right@ == right_range);
        
        // The multiset property follows from the loop invariants
        assert(final_range.to_multiset() == left@.to_multiset().add(right@.to_multiset()));
        assert(final_range.to_multiset() == left_range.to_multiset().add(right_range.to_multiset()));
    }
}

// Ex3 - Sort function using merge sort
fn sort(a: &mut Vec<int>)
    ensures
        a.len() == old(a).len(),
        sorted(a@),
        a@.to_multiset() == old(a)@.to_multiset()
{
    if a.len() <= 1 {
        return;
    }
    
    merge_sort_helper(a, 0, a.len());
}

// Helper function for merge sort
fn merge_sort_helper(a: &mut Vec<int>, l: usize, r: usize)
    requires
        l <= r,
        r <= a.len()
    ensures
        a.len() == old(a).len(),
        sorted(a@.subrange(l as int, r as int)),
        a@.subrange(0, l as int) == old(a)@.subrange(0, l as int),
        a@.subrange(r as int, a.len() as int) == old(a)@.subrange(r as int, old(a).len() as int),
        a@.subrange(l as int, r as int).to_multiset() == old(a)@.subrange(l as int, r as int).to_multiset()
    decreases r - l
{
    if r - l <= 1 {
        return;
    }
    
    let m = l + (r - l) / 2;
    
    proof {
        assert(l < m < r); // Help Verus prove the precondition for mergeArr
    }
    
    // Store the original array state for multiset reasoning
    proof {
        let orig_left = a@.subrange(l as int, m as int);
        let orig_right = a@.subrange(m as int, r as int);
        let orig_full = a@.subrange(l as int, r as int);
        assert(orig_full.to_multiset() == orig_left.to_multiset().add(orig_right.to_multiset()));
    }
    
    merge_sort_helper(a, l, m);
    
    proof {
        assert(sorted(a@.subrange(l as int, m as int)));
    }
    
    merge_sort_helper(a, m, r);
    
    proof {
        assert(sorted(a@.subrange(m as int, r as int)));
        assert(sorted(a@.subrange(l as int, m as int)));
    }
    
    mergeArr(a, l, m, r);
}

}