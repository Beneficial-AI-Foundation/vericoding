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


//IMPL remove_duplicates_from_sorted_array
method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
  requires is_sorted(nums)
  requires 1 <= |nums| <= 30000
  requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
  ensures is_sorted_and_distinct(result)
  ensures forall i :: i in nums <==> i in result
{
  result := [nums[0]];
  
  var idx := 1;
  while idx < |nums|
    invariant 1 <= idx <= |nums|
    invariant |result| >= 1
    invariant is_sorted_and_distinct(result)
    invariant forall i :: i in result ==> i in nums[0..idx]
    invariant forall i :: i in nums[0..idx] ==> i in result
    invariant result[|result|-1] == nums[idx-1]
  {
    if nums[idx] != nums[idx-1] {
      result := result + [nums[idx]];
    }
    idx := idx + 1;
  }
}