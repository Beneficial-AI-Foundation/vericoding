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
    // Convert multiset to sequence for processing
    let seq = m.to_seq();
    
    // Find the k-th smallest element by sorting
    let sorted_seq = sort_sequence(seq);
    let kth_element = sorted_seq[k as usize];
    
    // Partition the original multiset
    let pre = partition_less_than(m, kth_element);
    let post = partition_greater_equal(m, kth_element);
    
    (pre, kth_element, post)
}

// Helper function to sort a sequence
fn sort_sequence(seq: Seq<int>) -> (result: Seq<int>)
    ensures
        result.len() == seq.len(),
        forall |i: int| 0 <= i < seq.len() ==> seq[i] in result,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j]
{
    if seq.len() == 0 {
        seq
    } else if seq.len() == 1 {
        seq
    } else {
        // Simple insertion sort for verification
        insertion_sort(seq)
    }
}

// Helper function for insertion sort
fn insertion_sort(seq: Seq<int>) -> (result: Seq<int>)
    ensures
        result.len() == seq.len(),
        forall |i: int| 0 <= i < seq.len() ==> seq[i] in result,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j]
{
    let mut result = seq;
    let mut i = 1;
    
    while i < result.len()
        invariant
            result.len() == seq.len(),
            0 <= i <= result.len(),
            forall |idx: int| 0 <= idx < seq.len() ==> seq[idx] in result,
            forall |j: int, k: int| 0 <= j < k < i ==> result[j] <= result[k]
    {
        let key = result[i as usize];
        let mut j = i - 1;
        
        while j >= 0 && result[j as usize] > key
            invariant
                -1 <= j <= i - 1,
                result.len() == seq.len()
        {
            result = result.update(j as usize + 1, result[j as usize]);
            j = j - 1;
        }
        
        result = result.update(j as usize + 1, key);
        i = i + 1;
    }
    
    result
}

// Helper function to partition elements less than a value
spec fn partition_less_than(m: multiset<int>, val: int) -> multiset<int> {
    multiset_filter(m, |x: int| x < val)
}

// Helper function to partition elements greater than or equal to a value  
spec fn partition_greater_equal(m: multiset<int>, val: int) -> multiset<int> {
    multiset_filter(m, |x: int| x > val)
}

// Spec function to filter multiset
spec fn multiset_filter(m: multiset<int>, predicate: spec_fn(int) -> bool) -> multiset<int>;
{
}

}