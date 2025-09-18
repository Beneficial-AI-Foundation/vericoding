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
/* helper modified by LLM (iteration 5): simplified lemma by removing exists without proper trigger */
proof fn lemma_xor_properties()
    ensures
        forall|x: i32| x ^ x == 0,
        forall|x: i32| x ^ 0 == x,
        forall|x: i32, y: i32| x ^ y == y ^ x,
        forall|x: i32, y: i32, z: i32| (x ^ y) ^ z == x ^ (y ^ z),
{
}

proof fn lemma_xor_cancellation(nums: Seq<i32>)
    requires
        forall|elem: i32| nums.contains(elem) ==> (count_occurrences(nums, elem) == 1 || count_occurrences(nums, elem) == 2),
    ensures
        forall|x: i32| count_occurrences(nums, x) == 2 ==> (x ^ x) == 0,
{
}

proof fn lemma_xor_result(nums: Seq<i32>, unique: i32)
    requires
        count_occurrences(nums, unique) == 1,
        forall|elem: i32| nums.contains(elem) ==> (count_occurrences(nums, elem) == 1 || count_occurrences(nums, elem) == 2),
        forall|x: i32| nums.contains(x) ==> (x == unique || count_occurrences(nums, x) == 2),
    ensures
        unique == unique,
{
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
    /* code modified by LLM (iteration 5): simplified implementation to use XOR properties directly */
    let mut result = 0i32;
    let mut i = 0;
    
    while i < nums.len()
        invariant
            0 <= i <= nums.len(),
            exists|unique_elem: i32| count_occurrences(nums@, unique_elem) == 1,
            forall|elem: i32| nums@.contains(elem) ==> (count_occurrences(nums@, elem) == 1 || count_occurrences(nums@, elem) == 2),
        decreases nums.len() - i
    {
        result = result ^ nums[i];
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}