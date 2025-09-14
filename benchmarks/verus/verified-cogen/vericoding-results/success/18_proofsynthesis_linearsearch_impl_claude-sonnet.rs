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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut index: i32 = 0;
    while index < nums.len() as i32
        invariant
            0 <= index <= nums@.len(),
            forall |i: int| 0 <= i < index ==> nums@[i] != target,
        decreases nums@.len() - index
    {
        if nums[index as usize] == target {
            return index;
        }
        index = index + 1;
    }
    -1
}
// </vc-code>

}
fn main() {}