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
proof fn helper_find_single_number(nums: Seq<i32>, x1: i32, x2: i32) 
    requires
        nums.len() > 0,
        exists|unique_elem: i32| count_occurrences(nums, unique_elem) == 1,
        forall|elem: i32| nums.contains(elem) ==> (count_occurrences(nums, elem) == 1 || count_occurrences(nums, elem) == 2),
        x1 != x2,
        count_occurrences(nums, x1) == 2,
        count_occurrences(nums, x2) == 2
    ensures
        exists|r: i32| #[trigger] nums.contains(r) && r != x1 && r != x2 && count_occurrences(nums.filter(|y: i32| y != x1 && y != x2), r) == 1
{
    let filtered = nums.filter(|y: i32| y != x1 && y != x2);
    assert(filtered.len() > 0);
    assert(forall|elem: i32| filtered.contains(elem) ==> count_occurrences(nums, elem) == 1) by {
        forall|elem: i32|
            ensures filtered.contains(elem) ==> count_occurrences(nums, elem) == 1
        {
            if filtered.contains(elem) {
                assert(elem != x1 && elem != x2);
                assert(nums.contains(elem));
            }
        }
    };
    assert(exists|unique_elem: i32| count_occurrences(filtered, unique_elem) == 1) by {
        assert(exists|r: i32| count_occurrences(nums, r) == 1 && r != x1 && r != x2);
    };
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
{
    /* code modified by LLM (iteration 5): Fixed compilation by removing proof block from code section */
    let mut result = 0;
    for i in 0..nums.len() {
        result = result ^ nums[i];
    }
    result
}
// </vc-code>

}
fn main() {}