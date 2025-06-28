// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TwoSum(nums: Vec<int>, target: int) -> (r: (int, int))
    ensures
        0 <= r.0 ==> 0 <= r.0 < r.1 < nums.len() && 
            nums.spec_index(r.0) + nums.spec_index(r.1) == target &&
            forall i, j :: 0 <= i < j < r.1 ==> nums.spec_index(i) + nums.spec_index(j) != target,
        r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.len() ==> nums.spec_index(i) + nums.spec_index(j) != target
{
    return (0, 0);
}

}