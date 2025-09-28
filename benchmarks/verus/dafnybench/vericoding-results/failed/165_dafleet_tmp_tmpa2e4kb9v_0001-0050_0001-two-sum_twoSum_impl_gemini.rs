// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn correct_pair(pair: (int, int), nums: Seq<int>, target: int) -> bool {
    let (i, j) = pair;
    &&& 0 <= i < nums.len()
    &&& 0 <= j < nums.len()
    &&& i != j
    &&& nums[i] + nums[j] == target
}

spec fn seq_i32_to_int(s: Seq<i32>) -> Seq<int> {
    s.map(|i, v| v as int)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Reviewed and confirmed logic is sound. */
proof fn lemma_no_pair_found_implies_none_exists(nums: Seq<int>, target: int)
    requires
        forall|k: int, l: int| 0 <= k < nums.len() && k < l < nums.len() ==> nums[k] + nums[l] != target,
    ensures
        !exists|i: int, j: int| correct_pair((i, j), nums, target),
{
    if exists|i: int, j: int| correct_pair((i, j), nums, target) {
        let (i_wit, j_wit) = choose |i: int, j: int| correct_pair((i, j), nums, target);
        
        assert(correct_pair((i_wit, j_wit), nums, target));

        let k = if i_wit < j_wit { i_wit } else { j_wit };
        let l = if i_wit < j_wit { j_wit } else { i_wit };
        
        assert(i_wit != j_wit);
        assert(k < l);
        assert(0 <= k < nums.len());
        assert(0 <= l < nums.len());
        
        assert(nums[k] + nums[l] != target); // From requires
        
        assert(nums[i_wit] + nums[j_wit] == target); // From correct_pair spec
        assert(nums[k] + nums[l] == nums[i_wit] + nums[j_wit]);
        
        assert(false);
    }
}
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: Seq<i32>, target: i32) -> (pair: (usize, usize))
    requires exists|i: int, j: int| correct_pair((i, j), seq_i32_to_int(nums), target as int)
    ensures correct_pair((pair.0 as int, pair.1 as int), seq_i32_to_int(nums), target as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed a syntax error by changing 'ghost let' to 'let ghost'. */
    let ghost nums_int = seq_i32_to_int(nums);
    let ghost target_int = target as int;

    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            nums_int.len() == nums.len(),
            exists|a: int, b: int| correct_pair((a, b), nums_int, target_int),
            forall|k: int, l: int| 0 <= k < i as int && k < l < nums.len() ==> nums_int[k] + nums_int[l] != target_int,
        decreases nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                0 <= i < nums.len(),
                i < j <= nums.len(),
                nums_int.len() == nums.len(),
                exists|a: int, b: int| correct_pair((a, b), nums_int, target_int),
                forall|k: int, l: int| 0 <= k < i as int && k < l < nums.len() ==> nums_int[k] + nums_int[l] != target_int,
                forall|l: int| (i as int) < l < (j as int) ==> nums_int[i as int] + nums_int[l] != target_int,
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                return (i, j);
            }
            j = j + 1;
        }
        i = i + 1;
    }

    proof {
        lemma_no_pair_found_implies_none_exists(nums_int, target_int);
        assert(false);
    }
    unreachable!();
}
// </vc-code>

}
fn main() {}