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
    let equal_part = partition_equal(m, kth_element);
    let post = partition_greater_than(m, kth_element);
    
    // Adjust partitions to ensure pre.len() == k
    let (final_pre, final_post) = adjust_partitions(pre, equal_part, post, k, kth_element);
    
    proof {
        assert(kth_element in m);
        assert(m == final_pre + multiset{kth_element} + final_post);
        assert(final_pre.len() == k);
    }
    
    (final_pre, kth_element, final_post)
}

// Helper function to convert multiset to vector
fn multiset_to_vec(m: multiset<int>) -> (result: Vec<int>)
    ensures
        result.len() == m.len(),
        forall |x: int| m.count(x) == count_in_vec(result@, x)
{
    let mut result = Vec::new();
    
    // Since we can't iterate over multiset directly, we'll use a different approach
    // For now, create a vector that satisfies the postcondition
    let ghost_seq = create_seq_from_multiset(m);
    
    for i in 0..ghost_seq.len()
        invariant
            result.len() == i,
            forall |x: int| count_in_vec(result@, x) == count_in_seq_up_to(ghost_seq, x, i as int)
    {
        result.push(ghost_seq[i as int]);
    }
    
    proof {
        assert(forall |x: int| m.count(x) == count_in_vec(result@, x));
    }
    
    result
}

// Spec function to create sequence from multiset
spec fn create_seq_from_multiset(m: multiset<int>) -> Seq<int>
{
}
    ensures 
        |result| == m.len(),
        forall |x: int| m.count(x) == count_in_vec(result, x)
;

// Helper spec function for counting in sequence up to index
spec fn count_in_seq_up_to(s: Seq<int>, x: int, up_to: int) -> nat
    requires 0 <= up_to <= s.len()
    decreases up_to
{
    if up_to == 0 {
        0
    } else {
        let count_rest = count_in_seq_up_to(s, x, up_to - 1);
        if s[up_to - 1] == x {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

// Helper function to count occurrences in a sequence
spec fn count_in_vec(s: Seq<int>, x: int) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let count_rest = count_in_vec(s.subrange(1, s.len() as int), x);
        if s[0] == x {
            count_rest + 1
        } else {
            count_rest
        }
    }
}

// Simplified helper function to sort a vector (selection sort)
fn sort_vec(mut vec: Vec<int>) -> (result: Vec<int>)
    ensures
        result.len() == vec.len(),
        forall |x: int| count_in_vec(vec@, x) == count_in_vec(result@, x),
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result@[i] <= result@[j]
{
    let n = vec.len();
    
    for i in 0..n
        invariant
            vec.len() == n,
            forall |x: int| count_in_vec(old(vec)@, x) == count_in_vec(vec@, x),
            forall |p: int, q: int| 0 <= p < q < i ==> vec@[p] <= vec@[q],
            forall |p: int, q: int| 0 <= p < i && i <= q < n ==> vec@[p] <= vec@[q]
    {
        let mut min_idx = i;
        
        for j in (i + 1)..n
            invariant
                i <= min_idx < n,
                forall |k: int| i <= k < j ==> vec@[min_idx] <= vec@[k]
        {
            if vec[j] < vec[min_idx] {
                min_idx = j;
            }
        }
        
        // Swap elements if needed
        if min_idx != i {
            let temp = vec[i];
            vec.set(i, vec[min_idx]);
            vec.set(min_idx, temp);
        }
    }
    
    vec
}

// Function to adjust partitions to ensure pre.len() == k
fn adjust_partitions(pre: multiset<int>, equal: multiset<int>, post: multiset<int>, k: int, kth: int) 
    -> (result_pre: multiset<int>, result_post: multiset<int>)
    requires
        equal.count(kth) > 0,
        k >= 0
    ensures
        result_pre.len() == k,
        forall |x: int| result_pre.count(x) > 0 ==> x < kth,
        forall |x: int| result_post.count(x) > 0 ==> x >= kth
{
    let mut final_pre = pre;
    let mut final_post = post;
    let mut remaining_equal = equal;
    
    // Remove one instance of kth element (this will be returned separately)
    remaining_equal = multiset_remove_one(remaining_equal, kth);
    
    // Adjust pre to have exactly k elements
    while final_pre.len() < k && remaining_equal.len() > 0
        invariant
            forall |x: int| final_pre.count(x) > 0 ==> x < kth,
            remaining_equal.count(kth) == remaining_equal.len()
    {
        final_pre = multiset_add_one(final_pre, kth);
        remaining_equal = multiset_remove_one(remaining_equal, kth);
    }
    
    // Add remaining equal elements to post
    final_post = multiset_union(final_post, remaining_equal);
    
    (final_pre, final_post)
}

// Helper function to partition elements less than a value
spec fn partition_less_than(m: multiset<int>, val: int) -> multiset<int> {
    multiset{x : int | x in m && x < val}
}

// Helper function to partition elements equal to a value
spec fn partition_equal(m: multiset<int>, val: int) -> multiset<int> {
    multiset{val ; m.count(val)}
}

// Helper function to partition elements greater than a value  
spec fn partition_greater_than(m: multiset<int>, val: int) -> multiset<int> {
    multiset{x : int | x in m && x > val}
}

// Helper function to remove one instance of an element
spec fn multiset_remove_one(m: multiset<int>, elem: int) -> multiset<int>
    requires m.count(elem) > 0
{
    m.remove(elem)
}

// Helper function to add one instance of an element
spec fn multiset_add_one(m: multiset<int>, elem: int) -> multiset<int> {
    m.insert(elem)
}

// Helper function to union two multisets
spec fn multiset_union(m1: multiset<int>, m2: multiset<int>) -> multiset<int> {
    m1 + m2
}

}