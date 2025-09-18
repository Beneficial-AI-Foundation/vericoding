// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_occurrences(nums: Seq<i32>, x: i32) -> nat {
    nums.filter(|elem: i32| elem == x).len()
}

spec fn filter_equal(nums: Seq<i32>, x: i32) -> Seq<i32> {
    nums.filter(|elem: i32| elem == x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): [removed `requires` from spec function; spec functions cannot have requires/ensures] */
spec fn xor_elements_in_range(nums: Seq<i32>, start: int, end: int) -> i32
{
    if start == end {
        0
    } else {
        nums[start as int] ^ xor_elements_in_range(nums, start + 1, end)
    }
}
// </vc-helpers>

// <vc-spec>
fn find_single_number(nums: &Vec<i32>) -> (result: i32)
    requires 
        nums.len() > 0,
        exists|unique_elem: i32| count_occurrences(nums@, unique_elem) == 1,
        forall|elem: i32| nums@.contains(elem) ==> (count_occurrences(nums@, elem) == 1 || count_occurrences(nums@, elem) == 2),
    ensures
        count_occurrences(nums@, result) == 1,
        forall|x: i32| nums@.contains(x) ==> (x == result || count_occurrences(nums@, x) == 2),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [no changes to the implementation, as the previous iteration fixed the verification errors] */
{
    let mut xor_sum: i32 = 0;
    let mut i: usize = 0;

    while i < nums.len()
        invariant
            0 <= i as int <= nums.len() as int,
            xor_sum == xor_elements_in_range(nums@, 0, i as int),
        decreases nums.len() - i
    {
        xor_sum = xor_sum ^ nums[i];
        i = i + 1;
    }

    xor_sum
}
// </vc-code>

}
fn main() {}