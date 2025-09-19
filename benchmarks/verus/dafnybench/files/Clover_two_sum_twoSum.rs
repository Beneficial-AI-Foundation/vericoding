// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn twoSum(nums: &Vec<i8>, target: i8) -> (result: (usize, usize))
    requires 
        nums@.len() > 1,
        exists|i: int, j: int| 0 <= i < j < nums@.len() && nums@[i] + nums@[j] == target as int,
    ensures 
        0 <= result.0 < result.1 < nums@.len() && nums@[result.0 as int] + nums@[result.1 as int] == target as int
        && forall|ii: int, jj: int| #![trigger nums@[ii], nums@[jj]] (0 <= ii < result.0 && ii < jj < nums@.len()) ==> nums@[ii] + nums@[jj] != target as int
        && forall|jj: int| #![trigger nums@[jj]] result.0 < jj < result.1 ==> nums@[result.0 as int] + nums@[jj] != target as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}