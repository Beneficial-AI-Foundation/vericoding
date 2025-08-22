//ATOM
//https://leetcode.com/problems/remove-element/
method removeElement(nums: array<int>, val: int) returns (i: int)
  ensures forall k :: 0 < k < i < nums.Length ==> nums[k] != val
  modifies nums
{
  i := 0;
  assume forall k :: 0 < k < i < nums.Length ==> nums[k] != val;
  return i;
}

//IMPL
///compileTarget:js
method Main() {
  var elems := new int[5][1,2,3,4,5];
  var res := removeElement(elems, 5);
  print res, "\n", elems;
}