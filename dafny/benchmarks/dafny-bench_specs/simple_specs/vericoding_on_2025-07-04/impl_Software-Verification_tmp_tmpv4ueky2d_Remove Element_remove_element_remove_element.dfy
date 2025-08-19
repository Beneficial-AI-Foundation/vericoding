//IMPL 
method remove_element(nums: array<int>, val: int) returns (i: int)
  modifies nums
  requires 0 <= nums.Length <= 100
  requires forall i :: 0 <= i < nums.Length ==> 0 <= nums[i] <= 50
  requires 0 <= val <= 100
  ensures forall j :: 0 < j < i < nums.Length ==> nums[j] != val
{
  i := 0;
  var k := 0;
  
  while k < nums.Length
    invariant 0 <= i <= k <= nums.Length
    invariant forall j :: 0 < j < i ==> nums[j] != val
  {
    if nums[k] != val {
      nums[i] := nums[k];
      i := i + 1;
    }
    k := k + 1;
  }
}