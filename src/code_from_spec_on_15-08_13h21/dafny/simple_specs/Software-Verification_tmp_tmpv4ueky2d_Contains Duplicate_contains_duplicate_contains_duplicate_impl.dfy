//ATOM

predicate distinct(nums: seq<int>) {
  forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}


//IMPL 
method contains_duplicate(nums: seq<int>) returns (result: bool)
  requires 1 <= |nums| <= 100000
  requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
  ensures result <==> !distinct(nums)
{
  var i := 0;
  /* code modified by LLM (iteration 2): Fixed loop invariant to properly track distinctness of processed elements */
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant forall x, y :: 0 <= x < y < i ==> nums[x] != nums[y]
  {
    var j := 0;
    /* code modified by LLM (iteration 2): Check current element against all previous elements */
    while j < i
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < j ==> nums[k] != nums[i]
    {
      if nums[i] == nums[j] {
        /* code modified by LLM (iteration 2): Return true when duplicate found */
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  /* code modified by LLM (iteration 2): Return false when no duplicates found */
  result := false;
}