// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added overflow checking helper */
spec fn valid_indices(i: int, j: int, len: int) -> bool {
    0 <= i < len && 0 <= j < len && i != j
}

spec fn is_solution(nums: &Vec<i32>, i: usize, j: usize, target: i32) -> bool {
    i < j && j < nums.len() && nums[i as int] + nums[j as int] == target
}

spec fn is_first_solution(nums: &Vec<i32>, i: usize, j: usize, target: i32) -> bool {
    is_solution(nums, i, j, target) &&
    forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> nums[k1] + nums[k2] != target
}

spec fn no_overflow_add(a: i32, b: i32) -> bool {
    a as int + b as int >= i32::MIN as int && a as int + b as int <= i32::MAX as int
}
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: Vec<i32>, target: i32) -> (result: Option<(usize, usize)>)
    ensures
        match result {
            None => {
                forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> nums[i] + nums[j] != target
            },
            Some((i, j)) => {
                i < j &&
                j < nums.len() &&
                nums[i as int] + nums[j as int] == target &&
                forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> nums[k1] + nums[k2] != target
            }
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trigger annotation */
    let mut i = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall|k1: int, k2: int| 0 <= k1 < i && 0 <= k2 < nums.len() && k1 < k2 ==> nums[k1 as int] + nums[k2 as int] != target
        decreases nums.len() - i
    {
        let mut j = i + 1;
        while j < nums.len()
            invariant
                i < nums.len(),
                i + 1 <= j <= nums.len(),
                forall|k1: int, k2: int| 0 <= k1 < i && 0 <= k2 < nums.len() && k1 < k2 ==> nums[k1 as int] + nums[k2 as int] != target,
                forall|k2: int| i < k2 < j ==> nums[i as int] + nums[k2 as int] != target
            decreases nums.len() - j
        {
            if nums[i] + nums[j] == target {
                proof {
                    assert(i < j && j < nums.len());
                    assert(nums[i as int] + nums[j as int] == target);
                    assert(forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 && (k1 < i || (k1 == i && k2 < j)) ==> nums[k1] + nums[k2] != target);
                }
                return Some((i, j));
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert(forall|k1: int, k2: int| 0 <= k1 < nums.len() && 0 <= k2 < nums.len() && k1 < k2 ==> nums[k1] + nums[k2] != target);
        assert(forall|#[trigger] i: int, #[trigger] j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> i < j || j < i);
        assert(forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> nums[i] + nums[j] != target);
    }
    None
}
// </vc-code>

}
fn main() {}