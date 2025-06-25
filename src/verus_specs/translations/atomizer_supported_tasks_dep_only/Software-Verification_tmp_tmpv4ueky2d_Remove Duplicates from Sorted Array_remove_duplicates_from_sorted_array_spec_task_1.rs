pub fn remove_duplicates_from_sorted_array(nums: Seq<int>) -> (result: Seq<int>)
    requires(is_sorted(nums))
    requires(1 <= nums.len() <= 30000)
    requires(forall|i: int| 0 <= i < nums.len() ==> -100 <= nums[i] <= 100)
    ensures(is_sorted_and_distinct(result))
    ensures(forall|i: int| nums.contains(i) <==> result.contains(i))
{
}

spec fn is_sorted(nums: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]
}

spec fn is_sorted_and_distinct(nums: Seq<int>) -> bool
{
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j]
}