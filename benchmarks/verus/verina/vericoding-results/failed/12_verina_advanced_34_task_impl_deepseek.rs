// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add parentheses to function calls in assertions */
spec fn increasing_subsequence(seq: Seq<i32>, i: int, j: int) -> bool {
    forall|k: int, l: int| (i <= k < l <= j) ==> (seq[k] <= seq[l])
}

spec fn subsequence_length(seq: Seq<i32>, i: int, j: int) -> int {
    j - i + 1
}

proof fn lemma_increasing_subsequence_transitive(seq: Seq<i32>, a: int, b: int, c: int)
    requires
        0 <= a <= b <= c < seq.len(),
        increasing_subsequence(seq, a, b),
        increasing_subsequence(seq, b, c)
    ensures
        increasing_subsequence(seq, a, c)
{
    assert(forall|k: int, l: int| (a <= k < l <= c) implies (seq[k] <= seq[l]) by {
        if l <= b {
            assert(increasing_subsequence(seq, a, b));
        } else if k >= b {
            assert(increasing_subsequence(seq, b, c));
        } else {
            assert(increasing_subsequence(seq, a, b));
            assert(increasing_subsequence(seq, b, c));
            assert(seq[k] <= seq[b]);
            assert(seq[b] <= seq[l]);
        }
    });
}

proof fn lemma_single_element_increasing(seq: Seq<i32>, i: int)
    requires
        0 <= i < seq.len()
    ensures
        increasing_subsequence(seq, i, i)
{
    assert(forall|k: int, l: int| (i <= k < l <= i) implies (seq[k] <= seq[l]));
}

spec fn valid_index(vec: &Vec<i32>, i: int) -> bool {
    0 <= i < vec.len()
}

spec fn dp_vector_invariant(dp: &Vec<i32>, i: int) -> bool {
    0 <= i < dp.len() && dp[i] >= 1
}
// </vc-helpers>

// <vc-spec>
fn longest_increasing_subsequence(nums: &Vec<i32>) -> (result: i32)
    ensures
        result >= 0,
        result <= nums.len() as i32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fix syntax error by adding parentheses to assertion calls */
{
    let n = nums.len();
    let mut dp = Vec::<i32>::new();
    dp.resize(n, 0);
    
    let mut max_len = 0;
    
    let ghost seq = nums@;
    
    assert(forall|i: int| valid_index(nums, i) implies #[trigger] valid_index(&dp, i) by {
        assert(0 <= i < n);
    });
    
    for i in 0..n {
        assert(valid_index(nums, i));
        assert(valid_index(&dp, i));
        dp[i] = 1;
        
        for j in 0..i {
            assert(valid_index(nums, j));
            assert(valid_index(&dp, j));
            if nums[j] < nums[i] {
                if dp[j] + 1 > dp[i] {
                    dp[i] = dp[j] + 1;
                }
            }
        }
        
        if dp[i] > max_len {
            max_len = dp[i];
        }
    }
    
    assert(max_len >= 0);
    assert(max_len as int <= n);
    max_len
}
// </vc-code>

}
fn main() {}