method RemoveElement(nums: array<int>, val: int) returns (newLength: int)
  modifies nums
  ensures 0 <= newLength <= nums.Length
  ensures forall x :: x in nums[..newLength] ==> x != val
  ensures multiset(nums[..newLength]) == multiset(old(nums[..]))[val := 0]
{
  newLength := 0;
  var i := 0;
  
  /* code modified by LLM (iteration 4): Simplified loop invariants to track the correct multiset relationship */
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant 0 <= newLength <= i
    invariant forall x :: x in nums[..newLength] ==> x != val
    invariant multiset(nums[..newLength]) == multiset(old(nums[..i]))[val := 0]
  {
    if nums[i] != val {
      nums[newLength] := nums[i];
      newLength := newLength + 1;
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 4): Assert final condition to help prove postcondition */
  assert i == nums.Length;
  assert multiset(nums[..newLength]) == multiset(old(nums[..nums.Length]))[val := 0];
}