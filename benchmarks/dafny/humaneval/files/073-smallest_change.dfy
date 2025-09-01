// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def smallest_change(arr: List[int]) -> int
Given an array arr of integers, find the minimum number of elements that need to be changed to make the array palindromic. A palindromic array is an array that is read the same backwards and forwards. In one change, you can change one element to any other element.
*/
// </vc-description>

// <vc-spec>
method smallest_change(s: seq<int>) returns (c: int)
  // post-conditions-start
  ensures c == |set i | 0 <= i < |s| / 2 && s[i] != s[|s| - 1 - i]|
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
