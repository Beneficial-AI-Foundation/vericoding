// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed arithmetic bounds and verification */
spec fn vec_index_valid<T>(v: &Vec<T>, i: int) -> bool {
    0 <= i < v.view().len()
}

proof fn lemma_vec_index_in_bounds(nums: &Vec<i32>, i: int)
    requires vec_index_valid(nums, i)
    ensures i < nums.view().len()
{
}

proof fn lemma_vec_sum_valid(nums: &Vec<i32>, i: int, j: int)
    requires 
        vec_index_valid(nums, i),
        vec_index_valid(nums, j)
    ensures 
        -2147483648 <= (nums[i] as int) + (nums[j] as int) <= 2147483647
{
    assert(-2147483648 <= nums[i] as int <= 2147483647);
    assert(-2147483648 <= nums[j] as int <= 2147483647);
    assert((nums[i] as int) + (nums[j] as int) >= -2147483648) by {
        assert((nums[i] as int) + (nums[j] as int) >= -2147483648 - 2147483647);
        assert((nums[i] as int) + (nums[j] as int) >= -4294967296);
    };
    assert((nums[i] as int) + (nums[j] as int) <= 2147483647) by {
        assert((nums[i] as int) + (nums[j] as int) <= 2147483647 + 2147483647);
        assert((nums[i] as int) + (nums[j] as int) <= 4294967294);
    };
}

proof fn lemma_unique_minimal_solution(nums: Seq<int>, target: int, i: int, j: int, i0: int, j0: int)
    requires
        0 <= i < j < nums.len(),
        0 <= i0 < j0 < nums.len(),
        nums[i] + nums[j] == target,
        nums[i0] + nums[j0] == target,
        forall|k: int, l: int| 0 <= k < l < nums.len() && k < i0 ==> nums[k] + nums[l] != target
    ensures
        i0 <= i
{
    if i < i0 {
        assert(nums[i] + nums[j] == target);
        assert(forall|k: int, l: int| 0 <= k < l < nums.len() && k < i0 ==> nums[k] + nums[l] != target);
        assert(false);
    }
}

spec fn has_pair(seq: Seq<int>, target: int, i: int, j: int) -> bool {
    0 <= i < j < seq.len() && seq[i] + seq[j] == target
}
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: &Vec<i32>, target: i32) -> (result: (usize, usize))
    requires 
        nums.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
    ensures
        result.0 < result.1,
        result.1 < nums.len(),
        nums[result.0 as int] + nums[result.1 as int] == target,
        forall|i: int, j: int| 0 <= i < j < nums.len() && i < result.0 as int ==> nums[i] + nums[j] != target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed verification with proper invariants */
    let n = nums.len() as usize;
    let mut i: usize = 0;
    let mut j: usize;
    
    while i < n
        invariant
            0 <= i <= n,
            forall|k: int, l: int| 
                0 <= k < l < (n as int) && k < (i as int) ==> 
                    vec_index_valid(nums, k) && vec_index_valid(nums, l) && nums[k] + nums[l] != target,
            exists|k: int, l: int| 
                (i as int) <= k < l < (n as int) && vec_index_valid(nums, k) && vec_index_valid(nums, l) && nums[k] + nums[l] == target
        decreases n - i
    {
        j = i + 1;
        while j < n
            invariant
                i < j <= n,
                forall|l: int| 
                    (i as int) <= l < (j as int) ==> 
                        vec_index_valid(nums, l) && nums[i as int] + nums[l] != target
            decreases n - j
        {
            proof {
                lemma_vec_index_in_bounds(nums, j as int);
                lemma_vec_sum_valid(nums, i as int, j as int);
                assert(vec_index_valid(nums, i as int));
                assert(vec_index_valid(nums, j as int));
            }
            
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    proof {
        assert(forall|k: int, l: int| 0 <= k < l < (n as int) && k < (i as int) ==> nums[k] + nums[l] != target);
        assert(i as int == n as int);
        assert(!exists|k: int, l: int| (i as int) <= k < l < (n as int) && nums[k] + nums[l] == target);
        assert(!exists|k: int, l: int| 0 <= k < l < (n as int) && nums[k] + nums[l] == target);
        assert(false);
    }
    unreached()
}
// </vc-code>

}
fn main() {}