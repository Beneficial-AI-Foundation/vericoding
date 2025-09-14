// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn linear_search(nums: Vec<i32>, target: i32) -> (ret: i32)

    requires
        nums@.len() < 0x8000_0000,

    ensures
        ret < nums@.len(),
        ret >=0 ==> nums@[ret as int] == target,
        ret >=0 ==> forall |i: int| 0 <= i < ret as int ==> #[trigger]nums@[i]!= target,
        ret < 0 ==> forall |i: int| 0 <= i < nums@.len() as int ==> #[trigger]nums@[i] != target,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added precondition to loop invariant to prove cast safety and added trigger */
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            nums@.len() < 0x8000_0000,
            forall|j: int| 0 <= j < i as int ==> #[trigger]nums@[j] != target,
        decreases nums.len() - i
    {
        if nums[i] == target {
            return i as i32;
        }
        i = i + 1;
    }
    -1
}
// </vc-code>

}
fn main() {}