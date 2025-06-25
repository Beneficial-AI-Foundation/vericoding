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

spec fn InMap(nums: Seq<int>, m: map<int, int>, t: int) -> bool {
    forall j :: 0 <= j < nums.len() ==> t - nums.spec_index(j) in m
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