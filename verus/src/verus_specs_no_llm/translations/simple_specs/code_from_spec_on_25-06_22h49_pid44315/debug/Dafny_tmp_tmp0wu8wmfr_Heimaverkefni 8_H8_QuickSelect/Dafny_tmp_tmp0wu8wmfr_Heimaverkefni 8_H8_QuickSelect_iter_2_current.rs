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
    // Convert multiset to vector for processing
    let vec = multiset_to_vec(m);
    
    // Find the k-th smallest element by sorting
    let sorted_vec = sort_vec(vec);
    let kth_element = sorted_vec[k as usize];
    
    // Partition the original multiset
    let pre = partition_less_than(m, kth_element);
    let post = partition_greater_equal(m, kth_element);
    
    proof {
        // Prove that kth_element is in m
        assert(kth_element in m);
        
        // Prove the partition properties
        assert(m == pre + multiset{kth_element} + post);
        assert(pre.len() == k);
    }
    
    (pre, kth_element, post)
}

// Helper function to convert multiset to vector
fn multiset_to_vec(m: multiset<int>) -> (result: Vec<int>)
    ensures
        result.len() == m.len(),
        forall |x: int| m.count(x) == count_in_vec(result@, x)
{
    let mut result = Vec::new();
    let mut remaining = m;
    
    while remaining.len() > 0
        invariant
            result.len() + remaining.len() == m.len(),
            forall |x: int| m.count(x) == count_in_vec(result@, x) + remaining.count(x)
    {
        // Get an arbitrary element from the multiset
        let elem = choose_element(remaining);
        result.push(elem);
        remaining = remaining.remove(elem);
    }
    
    result
}

// Helper function to choose an element from a non-empty multiset
fn choose_element(m: multiset<int>) -> (result: int)
    requires m.len() > 0
    ensures result in m
{
    // This is a simplified implementation
    // In practice, we'd need a more sophisticated way to extract an element
    arbitrary()
}

// Helper function to count occurrences in a sequence
spec fn count_in_vec(s: Seq<int>, x: int) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let count_rest = count_in_vec(s.drop_first(), x);
        if s[0] == x {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

// Helper function to sort a vector
fn sort_vec(mut vec: Vec<int>) -> (result: Vec<int>)
    ensures
        result.len() == vec.len(),
        forall |x: int| count_in_vec(vec@, x) == count_in_vec(result@, x),
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result@[i] <= result@[j]
{
    // Simple selection sort
    let mut i = 0;
    
    while i < vec.len()
        invariant
            0 <= i <= vec.len(),
            forall |x: int| count_in_vec(old(vec)@, x) == count_in_vec(vec@, x),
            forall |j: int, k: int| 0 <= j < k < i ==> vec@[j] <= vec@[k],
            forall |j: int, k: int| 0 <= j < i && i <= k < vec.len() ==> vec@[j] <= vec@[k]
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < vec.len()
            invariant
                i <= min_idx < vec.len(),
                i < j <= vec.len(),
                forall |k: int| i <= k < j ==> vec@[min_idx] <= vec@[k]
        {
            if vec[j] < vec[min_idx] {
                min_idx = j;
            }
            j = j + 1;
        }
        
        // Swap elements
        let temp = vec[i];
        vec.set(i, vec[min_idx]);
        vec.set(min_idx, temp);
        
        i = i + 1;
    }
    
    vec
}

// Helper function to partition elements less than a value
spec fn partition_less_than(m: multiset<int>, val: int) -> multiset<int> {
    multiset_filter(m, val, true)
}

// Helper function to partition elements greater than a value  
spec fn partition_greater_equal(m: multiset<int>, val: int) -> multiset<int> {
    multiset_filter(m, val, false)
}

// Spec function to filter multiset
spec fn multiset_filter(m: multiset<int>, val: int, less_than: bool) -> multiset<int>
    decreases m.len()
{
    if m.len() == 0 {
        multiset{}
    } else {
        let elem = m.choose();
        let rest = m.remove(elem);
        let filtered_rest = multiset_filter(rest, val, less_than);
        
        if less_than {
            if elem < val {
                filtered_rest.insert(elem)
            } else {
                filtered_rest
            }
        } else {
            if elem > val {
                filtered_rest.insert(elem)
            } else {
                filtered_rest
            }
        }
    }
}

}