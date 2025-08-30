//ATOM

predicate distinct(nums: seq<int>) {
  forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}


// SPEC
method contains_duplicate(nums: seq<int>) returns (result: bool)
  requires 1 <= |nums| <= 100000
  requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
  ensures result <==> distinct(nums)
{
}
