// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn is_sorted(nums: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums.index(i) <= nums.index(j)
}
spec fn is_sorted_and_distinct(nums: Seq<int>) -> bool {
    forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums.index(i) < nums.index(j)
}

spec fn spec_remove_duplicates_from_sorted_array(nums: Seq<int>) -> result: seq<int>
    requires
        is_sorted(nums),
        1 <= nums.len() <= 30000,
        forall |i: int| 0 <= i < nums.len() ==> -100 <= nums.index(i) <= 100
    ensures
        is_sorted_and_distinct(result),
        forall |i: int| i in nums <==> i in result
;

proof fn lemma_remove_duplicates_from_sorted_array(nums: Seq<int>) -> (result: Seq<int>)
    requires
        is_sorted(nums),
        1 <= nums.len() <= 30000,
        forall |i: int| 0 <= i < nums.len() ==> -100 <= nums.index(i) <= 100
    ensures
        is_sorted_and_distinct(result),
        forall |i: int| i in nums <==> i in result
{
    Seq::empty()
}

}