//ATOM

predicate distinct(nums: seq<int>) {
  forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}


//IMPL 
method contains_duplicate(nums: seq<int>) returns (result: bool)
  requires 1 <= |nums| <= 100000
  requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
  ensures result <==> distinct(nums)
{
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    /* code modified by LLM (iteration 1): Changed invariant to properly express that all pairs in the range [0, i) are distinct */
    invariant forall x, y :: 0 <= x < y < i ==> nums[x] != nums[y]
  {
    var j := 0;
    /* code modified by LLM (iteration 1): Changed inner loop to check nums[i] against all previous elements nums[0..i) instead of nums[i+1..] */
    while j < i
      invariant 0 <= j <= i
      invariant forall x, y :: 0 <= x < y < i ==> nums[x] != nums[y]
      invariant forall k :: 0 <= k < j ==> nums[i] != nums[k]
    {
      if nums[i] == nums[j] {
        result := false;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := true;
}