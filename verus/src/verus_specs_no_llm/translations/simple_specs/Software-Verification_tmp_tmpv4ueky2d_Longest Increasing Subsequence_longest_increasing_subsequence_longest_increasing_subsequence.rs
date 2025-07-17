// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn find_max(x: int, y: int) -> int
{
    0
}

spec fn spec_longest_increasing_subsequence(nums: Vec<int>) -> max: int
    requires
        1 <= nums.len() <= 2500,
        forall |i: int| 0 <= i < nums.len() ==> -10000 <= nums.index(i) <= 10000
  // TODO: modify the
    ensures
        clause so that max is indeed equal to the longest increasing subsequence,
        max >= 1
;

proof fn lemma_longest_increasing_subsequence(nums: Vec<int>) -> (max: int)
    requires
        1 <= nums.len() <= 2500,
        forall |i: int| 0 <= i < nums.len() ==> -10000 <= nums.index(i) <= 10000
  // TODO: modify the
    ensures
        clause so that max is indeed equal to the longest increasing subsequence,
        max >= 1
{
    0
}

}