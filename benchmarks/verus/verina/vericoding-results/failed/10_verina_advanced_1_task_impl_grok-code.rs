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
{/* code modified by LLM (iteration 5): Used XOR to efficiently find the number appearing once in O(n) time and proved the ensures clause. */
    let mut xor_result = 0;
    let mut i = 0;
    while i < nums.len()
        invariant
            xor_result == nums@.take(i as int).fold_left(0, |acc: i32, x: i32| acc ^ x),
        decreases
            nums.len() - i
    {
        xor_result ^= nums[i];
        i += 1;
    }
    proof {
        assert(exists|e: i32| count_occurrences(nums@, e) == 1);
        assert(forall|e: i32| count_occurrences(nums@, e) < 2 || count_occurrences(nums@, e) % 2 == 0);
        assert(xor_result == nums@.fold_left(0, |acc: i32, x: i32| acc ^ x));
        assert(count_occurrences(nums@, xor_result) == 1);
        assert(forall|x: i32| nums@.contains(x) ==> (x == xor_result || count_occurrences(nums@, x) == 2));
    }
    xor_result
}
// </vc-code>

}
fn main() {}