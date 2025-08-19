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
/* code modified by LLM (iteration 1): Fixed Main method implementation to properly call removeElement and display results */
method Main() {
  var elems := new int[5](i => i + 1);  // Creates array [1,2,3,4,5];
  var res := removeElement(elems, 5);
  print res, "\n", elems[..];
}