// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn moves_to_make_zigzag(nums: Vec<nat>) -> (result: nat)
    ensures result >= 0,
    ensures nums.len() == 1 ==> result == 0,
    ensures result == 0 && nums.len() >= 2 ==> (
        forall|i: int| 1 <= i < nums.len() - 1 ==> (
            (nums[i] > nums[i-1] && nums[i] > nums[i+1]) ||
            (nums[i] < nums[i-1] && nums[i] < nums[i+1])
        )
    )

proof fn moves_nonnegative(nums: Vec<nat>)
    ensures moves_to_make_zigzag(nums) >= 0

proof fn single_element_zero(nums: Vec<nat>)
    requires nums.len() == 1
    ensures moves_to_make_zigzag(nums) == 0

proof fn zigzag_no_moves(nums: Vec<nat>, i: nat)
    requires nums.len() >= 2,
    requires moves_to_make_zigzag(nums) == 0,
    requires 1 <= i < nums.len() - 1
    ensures (nums[i] > nums[i-1] && nums[i] > nums[i+1]) ||
            (nums[i] < nums[i-1] && nums[i] < nums[i+1])

spec fn reverse_vec(nums: Seq<nat>) -> Seq<nat>
    decreases nums.len()
{
    if nums.len() == 0 {
        seq![]
    } else {
        reverse_vec(nums.drop_last()).push(nums[nums.len() - 1])
    }
}

proof fn symmetric_solution(nums: Vec<nat>)
    ensures moves_to_make_zigzag(nums) == moves_to_make_zigzag(reverse_vec(nums@).to_vec())
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0nat
    // impl-end
}

{
    // impl-start
    assume(false);
    // impl-end
}

{
    // impl-start
    assume(false);
    // impl-end
}

{
    // impl-start
    assume(false);
    // impl-end
}

{
    // impl-start
    assume(false);
    // impl-end
}
// </vc-code>


}

fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // Example usage (commented out for verification):
    // let result1 = moves_to_make_zigzag(vec![1, 2, 3]);
    // assert_eq!(result1, 2);
    
    // let result2 = moves_to_make_zigzag(vec![9, 6, 1, 6, 2]);
    // assert_eq!(result2, 4);
    
    // let result3 = moves_to_make_zigzag(vec![1]);
    // assert_eq!(result3, 0);
}