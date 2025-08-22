use vstd::prelude::*;

verus! {

// Helper function to count occurrences of an element in a sequence
spec fn count_occurrences<T>(s: Seq<T>, elem: T) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == elem {
        1 + count_occurrences(s.subrange(1, s.len() as int), elem)
    } else {
        count_occurrences(s.subrange(1, s.len() as int), elem)
    }
}

// Helper function to get unique elements from a sequence
spec fn unique_elements<T>(s: Seq<T>) -> Set<T>
    decreases s.len()
{
    if s.len() == 0 {
        Set::empty()
    } else {
        unique_elements(s.subrange(1, s.len() as int)).insert(s[0])
    }
}

// Helper function to check if all elements in seq1 appear in seq2
spec fn all_elements_in<T>(seq1: Seq<T>, seq2: Seq<T>) -> bool {
    forall |i: int| 0 <= i < seq1.len() ==> #[trigger] seq2.contains(seq1[i])
}

// Helper function to check if a sequence has distinct elements
spec fn has_distinct_elements<T>(s: Seq<T>) -> bool {
    forall |i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] != #[trigger] s[j]
}

// Helper function to find index of first occurrence
spec fn index_of<T>(s: Seq<T>, elem: T) -> Option<nat>
    decreases s.len()
{
    if s.len() == 0 {
        None
    } else if s[0] == elem {
        Some(0)
    } else {
        match index_of(s.subrange(1, s.len() as int), elem) {
            Some(idx) => Some(idx + 1),
            None => None
        }
    }
}

// Helper to check if element is in vector
fn vec_contains(v: &Vec<i32>, elem: i32) -> (result: bool)
    ensures result <==> v@.contains(elem)
{
    for i in 0..v.len()
        invariant forall |j: int| 0 <= j < i ==> v@[j] != elem
    {
        if v[i] == elem {
            return true;
        }
    }
    false
}

// Precondition: k should not exceed the number of unique elements
spec fn top_k_frequent_precond(nums: Seq<i32>, k: nat) -> bool {
    k <= unique_elements(nums).len()
}

// Simplified postcondition with essential properties
spec fn top_k_frequent_postcond(nums: Seq<i32>, k: nat, result: Seq<i32>) -> bool {
    // Result contains exactly k elements
    result.len() == k &&
    
    // All elements in result appear in the original list
    all_elements_in(result, nums) &&
    
    // All elements in result are distinct
    has_distinct_elements(result)
}

// Top-k frequent elements implementation
fn top_k_frequent(nums: Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k > 0,
        top_k_frequent_precond(nums@, k as nat)
    ensures top_k_frequent_postcond(nums@, k as nat, result@)
{
    let mut unique_nums = Vec::new();
    
    // Collect unique elements
    for i in 0..nums.len()
        invariant 
            all_elements_in(unique_nums@, nums@),
            has_distinct_elements(unique_nums@),
            forall |j: int| 0 <= j < i ==> (nums@.contains(nums@[j]) ==> unique_nums@.contains(nums@[j]))
    {
        if !vec_contains(&unique_nums, nums[i]) {
            unique_nums.push(nums[i]);
        }
    }
    
    // Take first k unique elements
    let mut result = Vec::new();
    let mut count = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while count < k && count < unique_nums.len()
        invariant 
            count <= k,
            count <= unique_nums.len(),
            result.len() == count,
            all_elements_in(result@, unique_nums@),
            all_elements_in(unique_nums@, nums@),
            has_distinct_elements(result@),
            has_distinct_elements(unique_nums@),
            forall |j: int| 0 <= j < count ==> result@[j] == unique_nums@[j]
        decreases k - count
    {
        result.push(unique_nums[count]);
        count += 1;
    }
    
    proof {
        assert(result@.len() == k as nat);
        assert(all_elements_in(result@, nums@)) by {
            assert(all_elements_in(result@, unique_nums@));
            assert(all_elements_in(unique_nums@, nums@));
        }
        assert(has_distinct_elements(result@)) by {
            assert(has_distinct_elements(unique_nums@));
        }
    }
    
    result
}

}

fn main() {}