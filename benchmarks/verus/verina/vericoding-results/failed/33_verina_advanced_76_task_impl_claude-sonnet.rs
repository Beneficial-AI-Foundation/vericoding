// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed saturating_sub and used simple arithmetic with guard */
use vstd::std_specs::hash::HashMapAdditionalSpecFns;

// Helper function to count frequencies of elements
fn count_frequencies(nums: &Vec<i32>) -> (result: std::collections::HashMap<i32, usize>)
    ensures
        forall|x: i32| result.contains_key(&x) <==> nums@.contains(x),
        forall|x: i32| result.contains_key(&x) ==> result.spec_index(x) > 0,
{
    let mut freq_map = std::collections::HashMap::new();
    let mut i = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall|j: usize| j < i ==> freq_map.contains_key(&nums[j as int]),
            forall|x: i32| freq_map.contains_key(&x) ==> nums@.subrange(0, i as int).contains(x),
    {
        let num = nums[i];
        let count = freq_map.get(&num).unwrap_or(&0);
        freq_map.insert(num, count + 1);
        i += 1;
    }
    freq_map
}

// Helper function to get top k elements by frequency
fn get_top_k_by_frequency(freq_map: std::collections::HashMap<i32, usize>, k: usize) -> (result: Vec<i32>)
    requires
        k <= freq_map.len(),
    ensures
        result.len() == k,
        result@.no_duplicates(),
        forall|x: i32| result@.contains(x) ==> freq_map.contains_key(&x),
{
    let mut pairs: Vec<(i32, usize)> = Vec::new();
    for (key, value) in freq_map.iter() {
        pairs.push((*key, *value));
    }
    
    // Sort by frequency in descending order using manual bubble sort
    let mut n = pairs.len();
    while n > 1
        invariant
            n <= pairs.len(),
    {
        let mut i = 0;
        while i < n && i + 1 < n
            invariant
                i <= n,
        {
            if pairs[i].1 < pairs[i + 1].1 {
                let temp = pairs[i];
                pairs.set(i, pairs[i + 1]);
                pairs.set(i + 1, temp);
            }
            i += 1;
        }
        n -= 1;
    }
    
    let mut result = Vec::new();
    let mut i = 0;
    while i < k && i < pairs.len()
        invariant
            i <= k,
            i <= pairs.len(),
            result.len() == i,
            result@.no_duplicates(),
    {
        result.push(pairs[i].0);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn top_k_frequent(nums: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k <= nums@.to_set().len(),
    ensures
        result.len() == k,
        forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        result@.no_duplicates(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): maintain implementation with fixed compilation errors */
    let freq_map = count_frequencies(nums);
    let result = get_top_k_by_frequency(freq_map, k);
    result
}
// </vc-code>

}
fn main() {}