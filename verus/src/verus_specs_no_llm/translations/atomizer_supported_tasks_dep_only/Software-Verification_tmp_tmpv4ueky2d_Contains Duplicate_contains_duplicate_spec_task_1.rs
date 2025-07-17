// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn distinct(nums: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums.index(i) != nums.index(j)
}

spec fn spec_contains_duplicate(nums: Seq<int>) -> result: bool
    requires
        1 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> -1000000000 <= nums.index(i) <= 1000000000
    ensures
        result <==> distinct(nums)
;

proof fn lemma_contains_duplicate(nums: Seq<int>) -> (result: bool)
    requires
        1 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> -1000000000 <= nums.index(i) <= 1000000000
    ensures
        result <==> distinct(nums)
{
    false
}

}