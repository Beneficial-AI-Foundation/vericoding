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
    // Get all elements as a sequence to work with
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
    // Use proof to establish the existence of such a sequence
    proof {
        let sorted_seq = choose |s: Seq<int>| {
            s.len() == m.len() &&
            (forall |i: int| 0 <= i < s.len() ==> s[i] in m) &&
            (forall |i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]) &&
            (forall |x: int| m.count(x) == seq_count(s, x))
        };
        assert(sorted_seq.len() == m.len());
        return sorted_seq;
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
    // Create the basic partitions
    let smaller = filter_smaller(m, kth);
    let equal_or_greater = filter_equal_or_greater(m, kth);
    
    // Remove one instance of kth for the return value
    let without_one_kth = equal_or_greater.remove(kth);
    let larger = filter_larger(without_one_kth, kth);
    let equal_remaining = filter_equal(without_one_kth, kth);
    
    // Build pre with exactly k elements
    let (pre_result, post_addition) = build_pre_exactly_k(smaller, equal_remaining, k);
    let post_result = larger + post_addition;
    
    proof {
        assert(m == pre_result + multiset{kth} + post_result);
    }
    
    (pre_result, post_result)
}

// Filter elements smaller than target
fn filter_smaller(m: multiset<int>, target: int) -> (result: multiset<int>)
    ensures
        forall |x: int| result.count(x) > 0 ==> x < target,
        forall |x: int| result.count(x) <= m.count(x),
        forall |x: int| x < target ==> result.count(x) == m.count(x)
{
    m.filter(|x: int| x < target)
}

// Filter elements equal to or greater than target
fn filter_equal_or_greater(m: multiset<int>, target: int) -> (result: multiset<int>)
    ensures
        forall |x: int| result.count(x) > 0 ==> x >= target,
        forall |x: int| result.count(x) <= m.count(x),
        forall |x: int| x >= target ==> result.count(x) == m.count(x)
{
    m.filter(|x: int| x >= target)
}

// Filter elements larger than target
fn filter_larger(m: multiset<int>, target: int) -> (result: multiset<int>)
    ensures
        forall |x: int| result.count(x) > 0 ==> x > target,
        forall |x: int| result.count(x) <= m.count(x),
        forall |x: int| x > target ==> result.count(x) == m.count(x)
{
    m.filter(|x: int| x > target)
}

// Filter elements equal to target
fn filter_equal(m: multiset<int>, target: int) -> (result: multiset<int>)
    ensures
        forall |x: int| result.count(x) > 0 ==> x == target,
        forall |x: int| result.count(x) <= m.count(x),
        result.count(target) == m.count(target)
{
    m.filter(|x: int| x == target)
}

// Build pre with exactly k elements
fn build_pre_exactly_k(smaller: multiset<int>, equal_remaining: multiset<int>, k: int) -> (pre: multiset<int>, leftover: multiset<int>)
    requires k >= 0
    ensures
        pre.len() == k,
        smaller + equal_remaining == pre + leftover,
        forall |x: int| pre.count(x) <= smaller.count(x) + equal_remaining.count(x)
{
    if smaller.len() >= k {
        // Take exactly k elements from smaller
        let (taken, remaining) = take_exactly_k(smaller, k);
        (taken, remaining + equal_remaining)
    } else {
        // Take all of smaller and some from equal_remaining
        let needed = k - smaller.len();
        let (taken_equal, remaining_equal) = take_exactly_k(equal_remaining, needed);
        (smaller + taken_equal, remaining_equal)
    }
}

// Take exactly k elements from multiset
fn take_exactly_k(m: multiset<int>, k: int) -> (taken: multiset<int>, remaining: multiset<int>)
    requires 
        k >= 0,
        k <= m.len()
    ensures
        taken.len() == k,
        m == taken + remaining,
        forall |x: int| taken.count(x) <= m.count(x),
        forall |x: int| remaining.count(x) <= m.count(x)
{
    proof {
        // Use proof to establish existence of such a partition
        let (result_taken, result_remaining) = choose |t: multiset<int>, r: multiset<int>| {
            t.len() == k &&
            m == t + r &&
            (forall |x: int| t.count(x) <= m.count(x)) &&
            (forall |x: int| r.count(x) <= m.count(x))
        };
        return (result_taken, result_remaining);
    }
}

}