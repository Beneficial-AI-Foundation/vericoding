// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn count_frequency(nums: Seq<i32>, elem: i32) -> (count: nat)
    ensures
        count <= nums.len(),
{
    if nums.len() == 0 {
        0
    } else {
        let last = nums[nums.len() as int - 1];
        let prefix = nums.subrange(0, nums.len() as int - 1);
        let prev_count = count_frequency(prefix, elem);
        if last == elem {
            prev_count + 1
        } else {
            prev_count
        }
    }
}

spec fn is_top_k_frequent(result: Seq<i32>, nums: Seq<i32>, k: nat) -> bool {
    &&& result.len() == k
    &&& result.no_duplicates()
    &&& forall|x: i32| result.contains(x) ==> nums.contains(x)
    &&& forall|x: i32| result.contains(x) ==> 
        (forall|y: i32| !result.contains(y) || count_frequency(nums, x) >= count_frequency(nums, y))
}

/* helper modified by LLM (iteration 5): Convert nat to usize safely */
fn nat_to_usize(n: nat) -> (usize_result: usize)
    ensures usize_result == n as usize,
{
    n as usize
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
    /* code modified by LLM (iteration 5): Fix int/nat casting issues */
    let mut frequency_map: Map<i32, u64> = Map::empty();
    let mut i: usize = 0;
    
    while i < nums.len()
        invariant
            i <= nums.len(),
            frequency_map.dom().finite(),
            forall|key: i32| frequency_map.dom().contains(key) ==> nums@.contains(key),
    {
        let num = nums[i];
        let count_option = frequency_map.get(num);
        let count = match count_option {
            Some(c) => c,
            None => 0,
        };
        frequency_map = frequency_map.insert(num, count + 1);
        i = i + 1;
    }
    
    let mut pairs: Vec<(i32, u64)> = Vec::new();
    let keys_seq = frequency_map.dom().to_seq();
    let mut j: usize = 0;
    
    while j < keys_seq.len()
        invariant
            j <= keys_seq.len(),
            pairs.len() == j,
    {
        let key = keys_seq[j];
        let count = frequency_map.get(key).unwrap_or(0);
        pairs.push((key, count));
        j = j + 1;
    }
    
    pairs.sort_by(|a, b| b.1.cmp(&a.1));
    
    let mut result: Vec<i32> = Vec::new();
    let mut m: usize = 0;
    
    while m < k
        invariant
            m <= k,
            result.len() == m,
            result@.no_duplicates(),
            forall|x: i32| result@.contains(x) ==> nums@.contains(x),
    {
        result.push(pairs[m].0);
        m = m + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}