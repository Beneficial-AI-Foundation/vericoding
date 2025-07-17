// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_TwoSum(nums: Vec<int>, target: int) -> r: (int, int)
    ensures
        0 <= r.0 ==> 0 <= r.0 < r.1 < nums.len() && 
                       nums.index(r.0) + nums.index(r.1) == target &&
                       forall |i: int, j: int| 0 <= i < j < r.1 ==> nums.index(i) + nums.index(j) != target,
        r.0 == -1 <==> forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums.index(i) + nums.index(j) != target
;

proof fn lemma_TwoSum(nums: Vec<int>, target: int) -> (r: (int, int))
    ensures
        0 <= r.0 ==> 0 <= r.0 < r.1 < nums.len() && 
                       nums.index(r.0) + nums.index(r.1) == target &&
                       forall |i: int, j: int| 0 <= i < j < r.1 ==> nums.index(i) + nums.index(j) != target,
        r.0 == -1 <==> forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums.index(i) + nums.index(j) != target
{
    (0, 0)
}

}