// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added decreases clauses to all loops */
spec fn count_occurrences(nums: Seq<i32>, value: i32) -> nat {
    nums.filter(|x: i32| x == value).len()
}

spec fn is_more_frequent(nums: Seq<i32>, a: i32, b: i32) -> bool {
    count_occurrences(nums, a) >= count_occurrences(nums, b)
}

fn count_in_vec(nums: &Vec<i32>, value: i32) -> (count: usize)
    ensures
        count == count_occurrences(nums@, value),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            count == count_occurrences(nums@.subrange(0, i as int), value),
        decreases nums.len() - i
    {
        if nums[i] == value {
            count = count + 1;
        }
        i = i + 1;
    }
    assert(nums@.subrange(0, nums.len() as int) =~= nums@);
    count
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
    /* code modified by LLM (iteration 5): Added decreases clauses to all while loops */
    let mut counts: Vec<(i32, usize)> = Vec::new();
    let mut processed: Vec<i32> = Vec::new();
    
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            processed@.no_duplicates(),
            forall|x: i32| processed@.contains(x) ==> nums@.contains(x),
            counts.len() == processed.len(),
            forall|j: int| 0 <= j < counts.len() ==> counts[j].0 == processed[j],
            forall|j: int| 0 <= j < counts.len() ==> counts[j].1 == count_occurrences(nums@, counts[j].0),
        decreases nums.len() - i
    {
        let current = nums[i];
        let mut already_processed = false;
        let mut j: usize = 0;
        while j < processed.len()
            invariant
                0 <= j <= processed.len(),
                already_processed <==> exists|k: int| 0 <= k < j && processed[k] == current,
            decreases processed.len() - j
        {
            if processed[j] == current {
                already_processed = true;
                break;
            }
            j = j + 1;
        }
        
        if !already_processed {
            let count = count_in_vec(nums, current);
            counts.push((current, count));
            processed.push(current);
        }
        i = i + 1;
    }
    
    let mut sorted_counts = counts;
    let mut i: usize = 0;
    while i < sorted_counts.len()
        invariant
            0 <= i <= sorted_counts.len(),
            sorted_counts.len() == counts.len(),
            forall|j: int| 0 <= j < sorted_counts.len() ==> sorted_counts@[j].0 == sorted_counts[j].0,
            forall|j: int| 0 <= j < sorted_counts.len() ==> nums@.contains(sorted_counts[j].0),
            forall|j: int| 0 <= j < sorted_counts.len() ==> sorted_counts[j].1 == count_occurrences(nums@, sorted_counts[j].0),
            forall|j: int, k: int| 0 <= j < i && i <= k < sorted_counts.len() ==> sorted_counts[j].1 >= sorted_counts[k].1,
        decreases sorted_counts.len() - i
    {
        let mut max_idx = i;
        let mut j: usize = i + 1;
        while j < sorted_counts.len()
            invariant
                i < j <= sorted_counts.len(),
                i <= max_idx < sorted_counts.len(),
                forall|m: int| i <= m < j ==> sorted_counts[max_idx as int].1 >= sorted_counts[m].1,
            decreases sorted_counts.len() - j
        {
            if sorted_counts[j].1 > sorted_counts[max_idx].1 {
                max_idx = j;
            }
            j = j + 1;
        }
        
        if max_idx != i {
            let temp = sorted_counts[i];
            sorted_counts.set(i, sorted_counts[max_idx]);
            sorted_counts.set(max_idx, temp);
        }
        i = i + 1;
    }
    
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i <= k,
            i <= sorted_counts.len(),
            result.len() == i,
            result@.no_duplicates(),
            forall|j: int| 0 <= j < i ==> result[j] == sorted_counts[j].0,
            forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        decreases k - i
    {
        result.push(sorted_counts[i].0);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}