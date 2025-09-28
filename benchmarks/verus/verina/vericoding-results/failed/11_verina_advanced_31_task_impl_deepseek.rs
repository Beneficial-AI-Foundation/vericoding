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
/* helper modified by LLM (iteration 5): Fix type mismatch issues in spec and provide proper int/usize conversion helpers */
proof fn max(a: int, b: int) -> (result: int)
    ensures
        result >= a,
        result >= b,
        result == a || result == b
{
    if a >= b {
        a
    } else {
        b
    }
}

spec fn dp_spec(xs: Seq<i32>, dp: Seq<int>, i: int) -> bool {
    forall|k: int| 0 <= k < i ==> 
        dp[k] >= 1 &&
        (forall|j: int| 0 <= j < k ==> xs[j] < xs[k] ==> dp[k] >= dp[j] + 1)
}

spec fn int_to_usize(n: int) -> usize {
    n as usize
}

spec fn usize_to_int(n: usize) -> int {
    n as int
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
/* code modified by LLM (iteration 5): Fix type conversions and ensure proper int/usize handling in while-loop invariants */
{
    let mut result = 0;
    let mut dp = vec![0; xs.len()];
    
    let mut i: usize = 0;
    while i < xs.len()
        invariant
            0 <= i <= xs.len(),
            result >= 0,
            dp.len() == xs.len(),
            forall|k: int| 0 <= k < usize_to_int(i) ==> dp[usize_to_int(k)] >= 1
        decreases xs.len() - i
    {
        dp[i] = 1;
        let mut j: usize = 0;
        while j < i
            invariant
                0 <= j <= i,
                dp[i] >= 1,
                forall|k: int| 0 <= k < usize_to_int(j) ==> xs[usize_to_int(k)] < xs[i] ==> dp[i] >= dp[usize_to_int(k)] + 1
            decreases i - j
        {
            if xs[j] < xs[i] {
                let candidate = dp[j] + 1;
                if candidate > dp[i] {
                    dp[i] = candidate;
                }
            }
            j += 1;
        }
        if dp[i] > result {
            result = dp[i];
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}