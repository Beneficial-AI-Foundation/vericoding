//ATOM

predicate distinct(nums: seq<int>) {
  forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}


//IMPL contains_duplicate
method contains_duplicate(nums: seq<int>) returns (result: bool)
  requires 1 <= |nums| <= 100000
  requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
  ensures result <==> distinct(nums)
{
  /* code modified by LLM (iteration 3): Initialize result to true (assume distinct initially) */
  result := true;
  
  /* code modified by LLM (iteration 3): Use nested loops to check all pairs */
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant result ==> forall x, y :: 0 <= x < y < |nums| && x < i ==> nums[x] != nums[y]
    invariant !result ==> !distinct(nums)
  {
    var j := i + 1;
    while j < |nums|
      invariant i < j <= |nums|
      invariant result ==> forall x, y :: 0 <= x < y < |nums| && x < i ==> nums[x] != nums[y]
      invariant result ==> forall k :: i < k < j ==> nums[i] != nums[k]
      invariant !result ==> !distinct(nums)
    {
      if nums[i] == nums[j] {
        /* code modified by LLM (iteration 3): Found duplicate, set result to false */
        result := false;
        /* code modified by LLM (iteration 3): Add assertion to help verification */
        assert i < j && nums[i] == nums[j];
        assert !distinct(nums);
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 3): Prove that no duplicates were found */
  assert forall x, y :: 0 <= x < y < |nums| ==> nums[x] != nums[y];
  assert distinct(nums);
  assert result <==> distinct(nums);
}