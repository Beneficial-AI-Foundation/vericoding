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
/* helper modified by LLM (iteration 5): Removed problematic nat/int conversion function */
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
/* code modified by LLM (iteration 5): Fixed ghost code usage by removing int casts and working directly with usize in loop */
{
    let mut xor_result = 0;
    let mut i: usize = 0;
    while i < nums.len()
        invariant
            xor_result == 0 || count_occurrences(nums@.subrange(0, i), xor_result) % 2 == 1,
            forall|x: i32| count_occurrences(nums@.subrange(0, i), x) % 2 == 1 ==> x == xor_result,
        decreases nums.len() - i,
    {
        xor_result = xor_result ^ nums[i];
        i = i + 1;
    }
    
    xor_result
}
// </vc-code>

}
fn main() {}