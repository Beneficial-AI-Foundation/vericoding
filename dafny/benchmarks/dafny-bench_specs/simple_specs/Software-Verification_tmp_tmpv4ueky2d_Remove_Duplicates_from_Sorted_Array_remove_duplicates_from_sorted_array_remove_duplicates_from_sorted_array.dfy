//ATOM


// Helper predicate
predicate is_sorted(nums: seq<int>)
{
  forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
}


//ATOM

predicate is_sorted_and_distinct(nums: seq<int>)
{
  forall i, j :: 0 <= i < j < |nums| ==> nums[i] < nums[j]
}


// SPEC
method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
  requires is_sorted(nums)
  requires 1 <= |nums| <= 30000
  requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
  ensures is_sorted_and_distinct(result)
  ensures forall i :: i in nums <==> i in result
{
}
