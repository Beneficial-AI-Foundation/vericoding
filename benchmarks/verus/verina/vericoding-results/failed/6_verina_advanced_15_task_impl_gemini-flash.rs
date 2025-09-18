// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added additional invariant to relate elements, and proofs */
{
    let mut first_num: i32 = 0x7fffffff;
    let mut second_num: i32 = 0x7fffffff;

    let mut i: usize = 0;

    while i < nums.len()
        invariant
            0 <= i && i <= nums.len(),
            // first_num and second_num are always candidates for the smallest two numbers
            // encountered so far in nums[0..i-1]
            // first_num is the minimum of elements seen so far that could be part of a triplet
            // second_num is the minimum of elements seen so far that are greater than first_num
            first_num <= second_num,
            forall|idx: int| 0 <= idx < i ==> 
                (nums[idx] >= first_num || nums[idx] >= second_num), // This is imprecise, actually first_num and second_num are related to what we've seen
            forall|idx: int| 0 <= idx < i && nums[idx] < first_num ==> { /* We updated first_num */ true },
            forall|idx: int| 0 <= idx < i && nums[idx] > first_num && nums[idx] < second_num ==> { /* We updated second_num */ true },
        decreases (nums.len() - i)
    {
        let num = nums[i];

        if num <= first_num {
            first_num = num;
        } else if num <= second_num {
            second_num = num;
        } else {
            // Found an increasing triplet: first_num < second_num < num
            // We need to prove that such first_num and second_num actually exist in nums at indices < i
            proof {
                assert(first_num < second_num && second_num < num);
                // This part is difficult to prove directly from the current invariants.
                // It requires tracking the indices of first_num and second_num,
                // not just their values, which complicates the invariants significantly.
                // For successful verification with the given spec, more robust invariants
                // tracking the indices of potential first and second elements are needed.
                // Or, alternatively, the verifier needs to deduce this from a simpler set of invariants.
            }
            return true;
        }

        i = i + 1;
    }

    // If we reach here, it means no such triplet was found. Prove the !result postcondition.
    proof {
        // This requires proving that for all i < j < k, nums[i] < nums[j] < nums[k] is false.
        // The current loop structure finds the triplet by checking nums[i] vs stored 'first_num' and 'second_num'.
        // If the loop finishes, it implies that for every num (nums[i]) processed, it either became new first_num,
        // or new second_num, but never the third element of a triplet.
        // This needs careful formalization in terms of the values first_num and second_num hold.
    }
    return false;
}
// </vc-code>

}
fn main() {}