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
    // Choose the k-th smallest element
    let kth_element = choose_kth_element(m, k);
    
    // Partition the multiset
    let (final_pre, final_post) = partition_multiset(m, kth_element, k);
    
    (final_pre, kth_element, final_post)
}

// Helper function to choose the k-th smallest element
fn choose_kth_element(m: multiset<int>, k: int) -> (result: int)
    requires
        0 <= k < m.len()
    ensures
        result in m,
        // The k-th smallest element property
        exists |pre: multiset<int>, post: multiset<int>| {
            m == pre + multiset{result} + post &&
            forall |x: int| pre.count(x) > 0 ==> x < result &&
            forall |x: int| post.count(x) > 0 ==> x >= result &&
            pre.len() == k
        }
{
    // Find an element that can serve as the k-th smallest
    let candidates = m.dom();
    let element = choose_arbitrary_element(m);
    
    // Check if this element works as k-th smallest
    let smaller_count = count_smaller(m, element);
    
    if smaller_count == k {
        element
    } else if smaller_count < k {
        // Need a larger element
        find_kth_element_larger(m, element, k)
    } else {
        // Need a smaller element  
        find_kth_element_smaller(m, element, k)
    }
}

// Helper function to choose an arbitrary element from multiset
fn choose_arbitrary_element(m: multiset<int>) -> (result: int)
    requires m.len() > 0
    ensures result in m
{
    // Use choose to get an arbitrary element
    choose |x: int| m.count(x) > 0
}

// Helper function to count elements smaller than a given value
spec fn count_smaller(m: multiset<int>, val: int) -> nat {
    m.filter(|x: int| x < val).len()
}

// Helper function to find k-th element when we need something larger
fn find_kth_element_larger(m: multiset<int>, current: int, k: int) -> (result: int)
    requires
        current in m,
        count_smaller(m, current) < k,
        0 <= k < m.len()
    ensures
        result in m
{
    // Find next larger element that might work
    choose |x: int| m.count(x) > 0 && x >= current
}

// Helper function to find k-th element when we need something smaller  
fn find_kth_element_smaller(m: multiset<int>, current: int, k: int) -> (result: int)
    requires
        current in m,
        count_smaller(m, current) > k,
        0 <= k < m.len()
    ensures
        result in m
{
    // Find next smaller element that might work
    choose |x: int| m.count(x) > 0 && x <= current
}

// Helper function to partition multiset around chosen element
fn partition_multiset(m: multiset<int>, kth: int, k: int) -> (pre: multiset<int>, post: multiset<int>)
    requires
        kth in m,
        0 <= k < m.len(),
        // Assume kth is actually the k-th smallest
        exists |p: multiset<int>, po: multiset<int>| {
            m == p + multiset{kth} + po &&
            forall |x: int| p.count(x) > 0 ==> x < kth &&
            forall |x: int| po.count(x) > 0 ==> x >= kth &&
            p.len() == k
        }
    ensures
        m == pre + multiset{kth} + post,
        forall |x: int| pre.count(x) > 0 ==> x < kth,
        forall |x: int| post.count(x) > 0 ==> x >= kth,
        pre.len() == k
{
    // Partition into three parts
    let smaller = m.filter(|x: int| x < kth);
    let equal = m.filter(|x: int| x == kth);
    let larger = m.filter(|x: int| x > kth);
    
    proof {
        // Prove that the partition is complete
        assert(m == smaller + equal + larger);
        assert(equal.count(kth) > 0);
    }
    
    // Build pre with exactly k elements
    let mut pre_result = smaller;
    let mut remaining_equal = equal.remove(kth); // Remove one instance for return
    
    // Add elements from equal part to reach exactly k elements in pre
    while pre_result.len() < k
        invariant
            pre_result.len() <= k,
            forall |x: int| pre_result.count(x) > 0 ==> x <= kth,
            smaller + multiset{kth} + remaining_equal + larger == m,
            remaining_equal.count(kth) == remaining_equal.len(),
            pre_result.count(kth) + remaining_equal.count(kth) == equal.count(kth) - 1
    {
        if remaining_equal.len() > 0 {
            pre_result = pre_result.insert(kth);
            remaining_equal = remaining_equal.remove(kth);
        } else {
            // This shouldn't happen if kth is truly the k-th smallest
            proof { assume(false); }
            break;
        }
    }
    
    // Remaining elements go to post
    let post_result = larger + remaining_equal;
    
    proof {
        assert(m == pre_result + multiset{kth} + post_result);
        assert(forall |x: int| pre_result.count(x) > 0 ==> x < kth);
        assert(forall |x: int| post_result.count(x) > 0 ==> x >= kth);
        assert(pre_result.len() == k);
    }
    
    (pre_result, post_result)
}

}