// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Avoid general pattern in closure, use loop instead */
    use std::collections::HashMap;
    let mut freq: HashMap<i32, usize> = HashMap::new();
    for num in nums.iter() {
        let count = freq.get(num).copied().unwrap_or(0) + 1;
        freq.insert(*num, count);
    }
    let mut count_vec = Vec::new();
    for item in freq.into_iter() {
        let (n, c) = item;
        count_vec.push((c, n));
    }
    count_vec.sort_by(|a, b| b.0.cmp(&a.0));
    let mut result = Vec::new();
    let len = if count_vec.len() < k { count_vec.len() } else { k };
    for i in 0..len {
        result.push(count_vec[i].1);
    }
    result
}
// </vc-code>

}
fn main() {}