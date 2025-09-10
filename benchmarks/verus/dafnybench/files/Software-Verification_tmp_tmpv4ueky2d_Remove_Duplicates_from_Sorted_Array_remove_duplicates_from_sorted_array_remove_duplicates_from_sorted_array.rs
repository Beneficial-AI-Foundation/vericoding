use vstd::prelude::*;

verus! {

spec fn is_sorted(nums: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]
}

spec fn is_sorted_and_distinct(nums: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j]
}

fn remove_duplicates_from_sorted_array(nums: Seq<int>) -> (result: Seq<int>)
    requires 
        is_sorted(nums),
        1 <= nums.len() <= 30000,
        forall|i: int| #![trigger nums[i]] 0 <= i < nums.len() ==> -100 <= nums[i] <= 100,
    ensures 
        is_sorted_and_distinct(result),
        forall|i: int| #![trigger nums.contains(i)] nums.contains(i) <==> result.contains(i),
{
    assume(false);
    unreached();
}

}
fn main() {}