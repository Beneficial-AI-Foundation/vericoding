// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn longest_increasing_subsequence(nums: Vec<int>) -> (max: int)
    requires
        1 <= nums.len() <= 2500,
        forall i :: 0 <= i < nums.len() ==> -10000 <= nums.spec_index(i) <= 10000
  // TODO: modify the
    ensures
        clause so that max is indeed equal to the longest increasing subsequence,
        max >= 1
{
    return 0;
}

}