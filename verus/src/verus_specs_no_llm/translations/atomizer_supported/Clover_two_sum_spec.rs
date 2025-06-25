// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn twoSum(nums: Vec<int>, target: int) -> (i: int, j: int)
    requires
        nums.len() > 1,
        exists i,j::0 <= i < j < nums.len() &&  nums.spec_index(i) + nums.spec_index(j) == target
    ensures
        0 <= i < j < nums.len() && nums.spec_index(i) + nums.spec_index(j) == target,
        forall ii,jj:: (0 <= ii < i && ii < jj < nums.len())  ==> nums.spec_index(ii) + nums.spec_index(jj) != target,
        forall jj:: i < jj < j ==> nums.spec_index(i) + nums.spec_index(jj) != target
{
    return (0, 0);
}

}