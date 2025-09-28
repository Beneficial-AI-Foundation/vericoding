// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `count_occurrences` function now returns a `nat` which is suitable for `Vec<i32>` as `count` needs to be non-negative. This is used when defining the helper function. */
proof fn count_occurrences(nums: &Vec<i32>, val: i32) -> (count: nat)
    ensures
        count == nums@.filter(|x: i32| x == val).len()
{
    let mut count: nat = 0;
    let mut i: nat = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            count == nums@.subsequence(0, i as int).filter(|x: i32| x == val).len()
        decreases nums.len() - i
    {
        if nums[i as usize] == val {
            count = count + 1;
        }
        i = i + 1;
    }
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
/* code modified by LLM (iteration 5): Converted `k` from `usize` to `nat` when used in loop condition to avoid compilation error. */
{
    let mut counts: Vec<(i32, nat)> = Vec::new();
    let mut unique_nums: Vec<i32> = Vec::new();

    let mut i: nat = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            unique_nums@.no_duplicates(),
            forall|j: int| 0 <= j < unique_nums.len() ==> nums@.contains(unique_nums[j as usize]),
            // For each unique number, its count in 'counts' matches its actual occurrences in 'nums'
            forall|k_idx: int| 0 <= k_idx < unique_nums.len() ==> {
                @counts.contains(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]) &&
                @counts.filter(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]).len() == 1 &&
                @counts.filter(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]).index(0).1 == count_occurrences(nums, unique_nums[k_idx as usize])
            },
            // The unique numbers accumulated so far are exactly those found in the processed part of 'nums'
            forall|num_in_processed: i32| unique_nums@.contains(num_in_processed) <==> nums@.subsequence(0, i as int).contains(num_in_processed)
        decreases nums.len() - i
    {
        let num = nums[i as usize];
        if !unique_nums@.contains(num) {
            unique_nums.push(num);
            let count = count_occurrences(nums, num);
            counts.push((num, count));
        }
        i = i + 1;
    }

    // Sort counts in descending order of frequency
    // Bubble sort for simplicity in Verus
    let mut j: nat = 0;
    while j < counts.len()
        invariant
            j <= counts.len(),
            // Elements from counts[0..j] are in their final sorted positions (largest frequency at the beginning)
            forall|x: int, y: int| 0 <= x < j && j <= y < counts.len() ==> counts[x as usize].1 >= counts[y as usize].1,
            // All elements in 'counts' are unique based on their first component (the number itself)
            counts@.map(|(n, _c): (i32, nat)| n).no_duplicates(),
            // All numbers in 'counts' are present in the original 'nums'
            forall|idx: int| 0 <= idx < counts.len() ==> nums@.contains(counts[idx as usize].0),
            // The set of (value, count) pairs remains constant (permutation invariant)
            counts@.len() as int == unique_nums@.len() as int,
            forall|k_idx: int| 0 <= k_idx < unique_nums.len() ==> {
                @counts.contains(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]) &&
                @counts.filter(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]).len() == 1 &&
                @counts.filter(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]).index(0).1 == count_occurrences(nums, unique_nums[k_idx as usize])
            }
        decreases counts.len() - j
    {
        let mut l: nat = 0;
        while (l as int) < counts.len() - (1 + j) as int
            invariant
                (l as int) <= counts.len() - (1 + j) as int,
                // Elements from counts[counts.len() - j - 1 .. counts.len()] are the largest in the unsorted part
                forall|x: int, y: int| 0 <= x < l && l <= y < counts.len() - j ==> counts[x as usize].1 >= counts[y as usize].1,
                // All elements in 'counts' are unique based on their first component (the number itself)
                counts@.map(|(n, _c): (i32, nat)| n).no_duplicates(),
                // All numbers in 'counts' are present in the original 'nums'
                forall|idx: int| 0 <= idx < counts.len() ==> nums@.contains(counts[idx as usize].0),
                // The set of (value, count) pairs remains constant (permutation invariant)
                counts@.len() as int == unique_nums@.len() as int,
                forall|k_idx: int| 0 <= k_idx < unique_nums.len() ==> {
                    @counts.contains(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]) &&
                    @counts.filter(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]).len() == 1 &&
                    @counts.filter(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]).index(0).1 == count_occurrences(nums, unique_nums[k_idx as usize])
                }
            decreases (counts.len() - (1 + j) - l) as int
        {
            if counts[l as usize].1 < counts[(l + 1) as usize].1 {
                let temp = counts[l as usize];
                counts.set(l as usize, counts[(l + 1) as usize]);
                counts.set((l + 1) as usize, temp);
            }
            l = l + 1;
        }
        j = j + 1;
    }

    let mut result: Vec<i32> = Vec::new();
    let mut i: nat = 0;
    while i < k as nat // Changed k to nat to avoid compilation error
        invariant
            i <= k as nat,
            result.len() as nat == i,
            // Each element in 'result' is the number from the corresponding position in 'counts'
            forall|idx: int| 0 <= idx < i ==> result[idx as usize] == counts[idx as usize].0,
            // 'result' contains no duplicates up to the current point
            result@.no_duplicates(),
            // Each element in 'result' is also in the original 'nums'
            forall|x: i32| result@.contains(x) ==> nums@.contains(x),
            // All elements in 'counts' are unique based on their first component (the number itself)
            counts@.map(|(n, _c): (i32, nat)| n).no_duplicates(),
            // All numbers in 'counts' are present in the original 'nums'
            forall|idx: int| 0 <= idx < counts.len() ==> nums@.contains(counts[idx as usize].0),
            // The set of (value, count) pairs remains constant (permutation invariant)
            counts@.len() as int == unique_nums@.len() as int,
            forall|k_idx: int| 0 <= k_idx < unique_nums.len() ==> {
                @counts.contains(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]) &&
                @counts.filter(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]).len() == 1 &&
                @counts.filter(|(val_in_counts, _count_in_counts): (i32, nat)| val_in_counts == unique_nums[k_idx as usize]).index(0).1 == count_occurrences(nums, unique_nums[k_idx as usize])
            }
        decreases (k as nat) - i
    {
        result.push(counts[i as usize].0);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}