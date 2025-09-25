// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn correct_pair(pair: (int, int), nums: Seq<int>, target: int) -> bool {
    let (i, j) = pair;
    &&& 0 <= i < nums.len()
    &&& 0 <= j < nums.len()
    &&& i != j
    &&& nums[i] + nums[j] == target
}

spec fn seq_i32_to_int(s: Seq<i32>) -> Seq<int> {
    s.map(|i, v| v as int)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: Seq<i32>, target: i32) -> (pair: (usize, usize))
    requires exists|i: int, j: int| correct_pair((i, j), seq_i32_to_int(nums), target as int)
    ensures correct_pair((pair.0 as int, pair.1 as int), seq_i32_to_int(nums), target as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}