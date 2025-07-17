// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_twoSum(nums: Vec<int>, target: int) -> i: int, j: int
    requires
        nums.len() > 1,
        exists |i: int, j: int|0 <= i < j < nums.len() && nums.index(i) + nums.index(j) == target
    ensures
        0 <= i < j < nums.len() && nums.index(i) + nums.index(j) == target,
        forall |ii: int, jj: int| (0 <= ii < i && ii < jj < nums.len()) ==> nums.index(ii) + nums.index(jj) != target,
        forall |jj: int| i < jj < j ==> nums.index(i) + nums.index(jj) != target
;

proof fn lemma_twoSum(nums: Vec<int>, target: int) -> (i: int, j: int)
    requires
        nums.len() > 1,
        exists |i: int, j: int|0 <= i < j < nums.len() && nums.index(i) + nums.index(j) == target
    ensures
        0 <= i < j < nums.len() && nums.index(i) + nums.index(j) == target,
        forall |ii: int, jj: int| (0 <= ii < i && ii < jj < nums.len()) ==> nums.index(ii) + nums.index(jj) != target,
        forall |jj: int| i < jj < j ==> nums.index(i) + nums.index(jj) != target
{
    (0, 0)
}

}