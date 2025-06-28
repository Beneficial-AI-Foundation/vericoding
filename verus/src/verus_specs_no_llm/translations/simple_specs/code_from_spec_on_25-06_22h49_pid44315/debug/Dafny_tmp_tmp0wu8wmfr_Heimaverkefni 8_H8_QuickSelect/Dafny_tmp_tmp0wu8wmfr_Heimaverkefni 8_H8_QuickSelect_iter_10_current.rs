use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn QuickSelect(m: multiset<int>, k: int) -> (pre: multiset<int>, kth: int, post: multiset<int>)
    requires
        0 <= k < m.len()
    ensures
        kth in m,
        m == pre + multiset{kth} + post,
        forall |x: int| pre.count(x) > 0 ==> x < kth,
        forall |x: int| post.count(x) > 0 ==> x >= kth,
        pre.len() == k
{
    // Get a sorted sequence representation
    let elements = multiset_to_sorted_seq(m);
    
    // The k-th element (0-indexed) in the sorted sequence
    let kth_element = elements[k as int];
    
    // Partition the multiset
    let (final_pre, final_post) = partition_multiset(m, kth_element, k);
    
    (final_pre, kth_element, final_post)
}

// Convert multiset to sorted sequence
fn multiset_to_sorted_seq(m: multiset<int>) -> (result: Seq<int>)
    requires m.len() > 0
    ensures 
        result.len() == m.len(),
        forall |i: int| 0 <= i < result.len() ==> result[i] in m,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        forall |x: int| m.count(x) == seq_count(result, x)
{
    // Convert to sequence and sort it
    let unsorted = multiset_to_seq(m);
    sort_sequence(unsorted)
}

// Convert multiset to sequence (unordered)
fn multiset_to_seq(m: multiset<int>) -> (result: Seq<int>)
    ensures
        result.len() == m.len(),
        forall |i: int| 0 <= i < result.len() ==> result[i] in m,
        forall |x: int| m.count(x) == seq_count(result, x)
{
    if m.len() == 0 {
        seq![]
    } else {
        // Pick an arbitrary element from the multiset
        let x = m.choose();
        let remaining = m.remove(x);
        let rest_seq = multiset_to_seq(remaining);
        seq![x] + rest_seq
    }
}

// Sort a sequence
fn sort_sequence(s: Seq<int>) -> (result: Seq<int>)
    ensures
        result.len() == s.len(),
        forall |i: int| 0 <= i < result.len() ==> result[i] in s,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        forall |x: int| seq_count(s, x) == seq_count(result, x)
{
    if s.len() <= 1 {
        s
    } else {
        // Simple insertion sort
        let first = s[0];
        let rest = s.subrange(1, s.len() as int);
        let sorted_rest = sort_sequence(rest);
        insert_sorted(first, sorted_rest)
    }
}

// Insert element into sorted sequence
fn insert_sorted(x: int, sorted: Seq<int>) -> (result: Seq<int>)
    requires
        forall |i: int, j: int| 0 <= i < j < sorted.len() ==> sorted[i] <= sorted[j]
    ensures
        result.len() == sorted.len() + 1,
        x in result,
        forall |y: int| y in sorted ==> y in result,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        seq_count(result, x) == seq_count(sorted, x) + 1,
        forall |y: int| y != x ==> seq_count(result, y) == seq_count(sorted, y)
{
    if sorted.len() == 0 {
        seq![x]
    } else if x <= sorted[0] {
        seq![x] + sorted
    } else {
        seq![sorted[0]] + insert_sorted(x, sorted.subrange(1, sorted.len() as int))
    }
}

// Count occurrences of element in sequence
spec fn seq_count(s: Seq<int>, x: int) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == x { 1 } else { 0 }) + seq_count(s.subrange(1, s.len() as int), x)
    }
}

// Helper function to partition multiset around chosen element
fn partition_multiset(m: multiset<int>, kth: int, k: int) -> (pre: multiset<int>, post: multiset<int>)
    requires
        kth in m,
        0 <= k < m.len()
    ensures
        m == pre + multiset{kth} + post,
        forall |x: int| pre.count(x) > 0 ==> x < kth,
        forall |x: int| post.count(x) > 0 ==> x >= kth,
        pre.len() == k
{
    // Remove one instance of kth
    let m_without_kth = m.remove(kth);
    
    // Partition into smaller and greater-equal
    let (smaller, greater_equal) = partition_around(m_without_kth, kth);
    
    // Build pre with exactly k elements
    let (pre_result, remaining) = build_pre_k_elements(smaller, greater_equal, k);
    
    (pre_result, remaining)
}

// Partition multiset around a pivot
fn partition_around(m: multiset<int>, pivot: int) -> (smaller: multiset<int>, greater_equal: multiset<int>)
    ensures
        m == smaller + greater_equal,
        forall |x: int| smaller.count(x) > 0 ==> x < pivot,
        forall |x: int| greater_equal.count(x) > 0 ==> x >= pivot
{
    if m.len() == 0 {
        (multiset{}, multiset{})
    } else {
        let x = m.choose();
        let rest = m.remove(x);
        let (rest_smaller, rest_greater_equal) = partition_around(rest, pivot);
        
        if x < pivot {
            (rest_smaller.insert(x), rest_greater_equal)
        } else {
            (rest_smaller, rest_greater_equal.insert(x))
        }
    }
}

// Build pre with exactly k elements
fn build_pre_k_elements(smaller: multiset<int>, greater_equal: multiset<int>, k: int) -> (pre: multiset<int>, remaining: multiset<int>)
    requires 
        k >= 0,
        k <= smaller.len() + greater_equal.len()
    ensures
        pre.len() == k,
        smaller + greater_equal == pre + remaining,
        forall |x: int| pre.count(x) > 0 ==> (smaller.count(x) > 0 || greater_equal.count(x) > 0),
        forall |x: int| remaining.count(x) > 0 ==> (smaller.count(x) > 0 || greater_equal.count(x) > 0)
{
    if k == 0 {
        (multiset{}, smaller + greater_equal)
    } else if smaller.len() >= k {
        // Take k elements from smaller
        take_k_elements(smaller, k, greater_equal)
    } else {
        // Take all of smaller and some from greater_equal
        let needed = k - smaller.len();
        let (taken_ge, remaining_ge) = take_k_elements(greater_equal, needed, multiset{});
        (smaller + taken_ge, remaining_ge)
    }
}

// Take exactly k elements from a multiset
fn take_k_elements(m: multiset<int>, k: int, extra: multiset<int>) -> (taken: multiset<int>, remaining: multiset<int>)
    requires 
        k >= 0,
        k <= m.len()
    ensures
        taken.len() == k,
        m + extra == taken + remaining,
        forall |x: int| taken.count(x) <= m.count(x) + extra.count(x),
        forall |x: int| remaining.count(x) <= m.count(x) + extra.count(x)
{
    if k == 0 {
        (multiset{}, m + extra)
    } else if m.len() == 0 {
        (multiset{}, extra)
    } else {
        let x = m.choose();
        let rest = m.remove(x);
        let (taken_rest, remaining_rest) = take_k_elements(rest, k - 1, extra);
        (taken_rest.insert(x), remaining_rest)
    }
}

}