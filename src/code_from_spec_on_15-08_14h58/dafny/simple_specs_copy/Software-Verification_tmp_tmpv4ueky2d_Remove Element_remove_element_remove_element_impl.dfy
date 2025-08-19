//IMPL
method remove_element(nums: array<int>, val: int) returns (i: int)
  modifies nums
  requires 0 <= nums.Length <= 100
  requires forall i :: 0 <= i < nums.Length ==> 0 <= nums[i] <= 50
  requires 0 <= val <= 100
  ensures forall j :: 0 < j < i < nums.Length ==> nums[j] != val
{
  if nums.Length == 0 {
    i := 0;
    return;
  }
  
  i := 1;
  var read := 1;
  
  while read < nums.Length
    invariant 1 <= i <= nums.Length
    invariant 1 <= read <= nums.Length
    invariant i <= read
    invariant forall j :: 1 <= j < i ==> nums[j] != val
  {
    if nums[read] != val {
      nums[i] := nums[read];
      i := i + 1;
    }
    read := read + 1;
  }
}