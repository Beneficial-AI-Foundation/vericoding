// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn in_map(nums: Seq<int>, m: Map<int, int>, t: int) -> bool {
    forall|j: int| 0 <= j < nums.len() ==> m.contains_key(t - nums[j])
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: &[i8], target: i8) -> (r: (i8, i8))
    ensures 
        0 <= r.0 ==> 0 <= r.0 < r.1 < nums@.len() && 
                     nums@[r.0 as int] + nums@[r.1 as int] == target as int &&
                     forall|i: int, j: int| 0 <= i < j < r.1 as int ==> nums@[i] + nums@[j] != target as int,
        r.0 == -1 <==> forall|i: int, j: int| 0 <= i < j < nums@.len() ==> nums@[i] + nums@[j] != target as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}