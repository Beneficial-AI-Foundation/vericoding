// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_subsequence_of(subseq: Seq<i32>, seq: Seq<i32>) -> bool {
    exists|indices: Seq<int>| 
        indices.len() == subseq.len() &&
        #[trigger] indices.len() >= 0 &&
        (forall|i: int| 0 <= i < indices.len() ==> #[trigger] indices[i] >= 0 && indices[i] < seq.len()) &&
        (forall|i: int| 0 <= i < indices.len() - 1 ==> #[trigger] indices[i] < indices[i + 1]) &&
        (forall|i: int| 0 <= i < subseq.len() ==> #[trigger] subseq[i] == seq[indices[i]])
}

spec fn is_strictly_increasing(seq: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < seq.len() - 1 ==> #[trigger] seq[i] < seq[i + 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding back the original helper code for `find_insertion_point` that performs a binary search, as it was removed in previous iterations. No other changes are needed for the helper section to address the current compilation problem. */
proof fn find_insertion_point(actual_dp_seq: Seq<i32>, low: int, high: int, x: i32) -> (mid: int)
    requires
        0 <= low <= high < actual_dp_seq.len(),
        // actual_dp_seq is sorted
        (forall |j: int| low <= j < high ==> actual_dp_seq[j as int] < actual_dp_seq[j + 1 as int]),
    ensures
        low <= mid <= high,
        actual_dp_seq[mid] >= x,
        (mid == 0 || actual_dp_seq[mid - 1] < x)
{
    let mut l = low;
    let mut r = high;
    let mut ans = high;

    while l <= r
        invariant
            low <= l <= high + 1,
            low - 1 <= r <= high,
            l <= r + 1,
            low <= ans <= high,
            // actual_dp_seq is sorted
            (forall |j: int| low <= j < high ==> actual_dp_seq[j as int] < actual_dp_seq[j + 1 as int]),
            // anything to the left of l is less than x
            (forall |j: int| 0 <= j < l ==> actual_dp_seq[j as int] < x),
            // ans is a valid candidate and satisfies the condition actual_dp_seq[ans] >= x
            actual_dp_seq[ans] >= x,
            // anything to the right of r might be >= x
            (forall |j: int| r < j <= high ==> actual_dp_seq[j as int] >= x),

        decreases r - l
    {
        let mid = l + (r - l) / 2;
        if actual_dp_seq[mid] >= x {
            ans = mid;
            r = mid - 1;
        } else {
            l = mid + 1;
        }
    }
    ans
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subseq_length(xs: &Vec<i32>) -> (result: usize)
    ensures

        exists|subseq: Seq<i32>| 
            is_subsequence_of(subseq, xs@) && 
            is_strictly_increasing(subseq) && 
            subseq.len() == result,

        forall|subseq: Seq<i32>| 
            (is_subsequence_of(subseq, xs@) && is_strictly_increasing(subseq)) 
            ==> subseq.len() <= result,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed a compilation error regarding a missing comma after the first `forall` quantifier within the `while` loop's `invariant` block. Also, changed the hardcoded 0_usize to `0` for the return value when `n == 0`, because it doesn't need to be `usize` in that case, `usize` is already infered by the function return type. */
{
    let n = xs.len();
    if n == 0 {
        return 0;
    }

    let mut dp: Vec<usize> = Vec::new();
    let mut actual_dp: Vec<i32> = Vec::new(); // Stores the smallest ending element of an increasing subsequence of length i+1

    // Initialize dp with a sentinel value indicating no increasing subsequence of that length yet
    for _ in 0..n {
        dp.push(0);
        actual_dp.push(0);
    }

    dp[0] = 1;
    actual_dp[0] = xs[0];
    let mut max_len = 1;

    for i in 1..n {
        let x = xs[i];
        if x > actual_dp[max_len - 1] {
            // x extends the longest increasing subsequence found so far
            dp[max_len] = max_len + 1;
            actual_dp[max_len] = x;
            max_len = max_len + 1;
        } else {
            // Find the first element in actual_dp that is >= x
            // This uses a binary search like approach to find the correct position to update
            // 'pos' will be the length of the LIS that x can potentially extend or replace
            let mut low: usize = 0;
            let mut high: usize = max_len - 1;
            let mut pos: usize = max_len - 1;

            while low <= high
                invariant
                    low <= high + 1,
                    pos < max_len,
                    low <= pos + 1,
                    high < actual_dp.len(),
                    (forall |j: int| 0 <= j < low ==> actual_dp[j as usize] as int < x as int),
                    (forall |j: int| high < j < actual_dp.len() ==> actual_dp[j as usize] as int >= x as int),
                decreases high - low
            {
                let mid = low + (high - low) / 2;
                if actual_dp[mid] < x {
                    low = mid + 1;
                } else {
                    pos = mid;
                    if mid == 0 {
                        break;
                    }
                    high = mid - 1;
                }
            }
            actual_dp[pos] = x;
        }
    }
    max_len
}
// </vc-code>

}
fn main() {}