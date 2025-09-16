// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): valid_index checks index bounds */
spec fn valid_index(len: nat, i: int) -> bool { 0 <= i < len }
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn pairs_sum_to_zero(nums: &[i32], target: i32) -> (found: bool)

    requires
        nums.len() >= 2,
        forall|i: int, j: int|
            0 <= i < j < nums.len() ==> nums[i] + nums[j] <= i32::MAX && nums[i] + nums[j]
                >= i32::MIN,

    ensures
        found <==> exists|i: int, j: int| 0 <= i < j < nums.len() && nums[i] + nums[j] == target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid int casts in runtime by using i32 arithmetic and prove existence in proof block */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall|p: int, q: int|
                0 <= p < q < nums.len() && (p < i as int) ==> nums@[p] + nums@[q] != target,
        decreases
            nums.len() - i
    {
        let mut j: usize = i + 1;
        while j < nums.len()
            invariant
                i <= nums.len(),
                j >= i + 1,
                j <= nums.len(),
                forall|p: int, q: int|
                    0 <= p < q < nums.len() && (p < i as int || (p == i as int && q < j as int)) ==> nums@[p] + nums@[q] != target,
            decreases
                nums.len() - j
        {
            if nums[i] + nums[j] == target {
                proof {
                    assert(j < nums.len());
                    let ii: int = i as int;
                    let jj: int = j as int;
                    assert(0 <= ii && ii < jj && jj < nums.len() as int);
                    assert(nums@[ii] + nums@[jj] == target);
                }
                return true;
            }
            j += 1;
        }
        i += 1;
    }
    proof {
        assert(forall|p: int, q: int| 0 <= p < q < nums.len() ==> nums@[p] + nums@[q] != target);
    }
    false
}
// </vc-code>

}
fn main() {}