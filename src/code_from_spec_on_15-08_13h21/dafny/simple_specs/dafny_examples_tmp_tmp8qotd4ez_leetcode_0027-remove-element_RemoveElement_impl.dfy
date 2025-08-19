method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
  modifies nums
  ensures 0 <= newLength <= nums.Length
  ensures forall x :: x in nums[..newLength] ==> x != val
  ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{
  newLength := 0;
  var i := 0;
  
  /* code modified by LLM (iteration 4): replaced multiset multiplication with proper multiset operations using helper function */
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant 0 <= newLength <= i
    invariant forall k :: 0 <= k < newLength ==> nums[k] != val
    invariant multiset(nums[..newLength]) + RepeatMultiset(val, i - newLength) == multiset(old(nums[..i]))
  {
    if nums[i] != val {
      nums[newLength] := nums[i];
      newLength := newLength + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): replaced multiset multiplication with proper multiset operations using helper function */
  assert multiset(nums[..newLength]) + RepeatMultiset(val, nums.Length - newLength) == multiset(old(nums[..]));
}

/* code modified by LLM (iteration 4): added helper function to create multiset with repeated elements */
function RepeatMultiset(val: int, count: int): multiset<int>
  requires count >= 0
{
  if count == 0 then multiset{} else multiset{val} + RepeatMultiset(val, count - 1)
}