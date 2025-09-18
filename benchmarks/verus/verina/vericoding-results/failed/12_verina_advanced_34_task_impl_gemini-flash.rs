// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error (missing comma) in 'is_increasing_subsequence' spec */
proof fn is_increasing_subsequence(original_seq: &Vec<i32>, sub_seq: &Vec<i32>) -> (result: bool)
    requires
        original_seq.len() >= 0,
        sub_seq.len() >= 0,
    ensures
        result == ( {
            &&& sub_seq.len() <= original_seq.len()
            &&& (forall j: int where 0 <= j && j < sub_seq.len() - 1 predicts sub_seq.nonlinear_index(j) < sub_seq.nonlinear_index(j+1)),
            &&& (forall j: int where 0 <= j && j < sub_seq.len() implies (exists i: int where 0 <= i && i < original_seq.len() && original_seq.nonlinear_index(i) == sub_seq.nonlinear_index(j)))
        })
{
    if sub_seq.len() == 0 {
        true
    } else if sub_seq.len() == 1 {
        exists |i: int| 0 <= i && i < original_seq.len() && original_seq.nonlinear_index(i) == sub_seq.nonlinear_index(0)
    } else {
        let mut current_idx: int = 0;
        let mut original_current_idx: int = 0;
        let mut is_monotonic = true;
        while current_idx < sub_seq.len()
            invariant
                0 <= current_idx <= sub_seq.len(),
                0 <= original_current_idx <= original_seq.len(),
                is_monotonic, // The 'implies' was incorrect in previous iteration, making the condition always evaluate 'false'
                current_idx == 0 || (exists i: int where 0 <= i && i < original_seq.len() && original_seq.nonlinear_index(i) == sub_seq.nonlinear_index(current_idx-1)),
            decreases sub_seq.len() - current_idx
        {
            if current_idx > 0 && sub_seq.nonlinear_index(current_idx - 1) >= sub_seq.nonlinear_index(current_idx) {
                is_monotonic = false;
            }

            let mut found = false;
            while original_current_idx < original_seq.len()
                invariant
                    0 <= current_idx < sub_seq.len(),
                    0 <= original_current_idx <= original_seq.len(),
                    is_monotonic,
                    found == false,
                    current_idx == 0 || (exists i_prev: int where 0 <= i_prev && i_prev < original_seq.len() && original_seq.nonlinear_index(i_prev) == sub_seq.nonlinear_index(current_idx - 1)),

                decreases original_seq.len() - original_current_idx
            {
                if original_seq.nonlinear_index(original_current_idx) == sub_seq.nonlinear_index(current_idx) {
                    found = true;
                    break;
                }
                original_current_idx = original_current_idx + 1;
            }
            if !found {
                return false;
            }
            original_current_idx = original_current_idx + 1; // Start searching from the next element in the original sequence
            current_idx = current_idx + 1;
        }

        is_monotonic
    }
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= nums.len() as i32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The original code was empty. This new code implements the O(n^2) dynamic programming solution for LIS. It initializes a DP array and iteratively calculates the longest increasing subsequence ending at each position, then finds the maximum among them. */
{
    let n = nums.len() as int;

    if n == 0 {
        return 0i32;
    }

    let mut dp: Vec<i32> = Vec::new();

    // Initialize dp with 1 for each number. The LIS ending at nums[i] is at least 1 (the number itself).
    let mut i = 0;
    while i < n
        invariant 0 <= i <= n,
            dp.len() == i,
            (forall k: int where 0 <= k < i implies dp.nonlinear_index(k) == 1),
        decreases n - i
    {
        dp.push(1i32);
        i = i + 1;
    }

    let mut max_len = 1i32;

    let mut i = 1;
    while i < n
        invariant 0 <= i <= n,
            dp.len() == n,
            max_len >= 1,
            (forall k: int where 0 <= k < i implies dp.nonlinear_index(k) >= 1),
            (forall k: int where 0 <= k < i implies dp.nonlinear_index(k) <= k + 1),
        decreases n - i
    {
        let mut j = 0;
        while j < i
            invariant 0 <= j <= i,
                dp.len() == n,
                max_len >= 1,
                (forall k: int where 0 <= k < i implies dp.nonlinear_index(k) >= 1),
                (forall k: int where 0 <= k < i implies dp.nonlinear_index(k) <= k + 1),
                (forall k: int where 0 <= k < j implies (
                    (nums.nonlinear_index(i) > nums.nonlinear_index(k) ==> dp.nonlinear_index(i) >= dp.nonlinear_index(k) + 1)
                    && nums.nonlinear_index(i) > nums.nonlinear_index(k) // Added a conjunct to keep the invariant simple
                )),
            decreases i - j
        {
            if nums.nonlinear_index(i) > nums.nonlinear_index(j) {
                let potential_len = dp.nonlinear_index(j) + 1;
                if potential_len > dp.nonlinear_index(i) {
                    dp.set(i, potential_len);
                }
            }
            j = j + 1;
        }

        if dp.nonlinear_index(i) > max_len {
            max_len = dp.nonlinear_index(i);
        }
        i = i + 1;
    }

    max_len
}
// </vc-code>

}
fn main() {}