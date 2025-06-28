// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn twoSum(nums: Seq<int>, target: int) -> (pair: (int, int))
    requires
        exists i, j :: correct_pair((i, j), nums, target)
    ensures
        correct_pair(pair, nums, target)
{
    return (0, 0);
}

}