use vstd::prelude::*;

verus! {

spec fn distinct(nums: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j]
}

fn contains_duplicate(nums: Seq<int>) -> (result: bool)
    requires
        1 <= nums.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] >= -1000000000 && nums[i] <= 1000000000,
    ensures
        result <==> distinct(nums),
{
    assume(false);
    unreached();
}

}
fn main() {}