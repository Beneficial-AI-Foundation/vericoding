// <vc-helpers>
function count_changes_needed(arr: seq<int>, left: int, right: int): int
  requires 0 <= left <= right < |arr|
  decreases right - left
{
  if left >= right then 0
  else if arr[left] == arr[right] then count_changes_needed(arr, left + 1, right - 1)
  else 1 + count_changes_needed(arr, left + 1, right - 1)
}

lemma count_changes_bounded(arr: seq<int>, left: int, right: int)
  requires 0 <= left <= right < |arr|
  ensures count_changes_needed(arr, left, right) <= (right - left + 1) / 2
  decreases right - left
{
  if left >= right {
  } else {
    count_changes_bounded(arr, left + 1, right - 1);
  }
}

lemma count_changes_main_bounded(arr: seq<int>)
  requires |arr| > 0
  ensures count_changes_needed(arr, 0, |arr| - 1) <= |arr| / 2
{
  count_changes_bounded(arr, 0, |arr| - 1);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def smallest_change(arr: List[int]) -> int
Given an array arr of integers, find the minimum number of elements that need to be changed to make the array palindromic. A palindromic array is an array that is read the same backwards and forwards. In one change, you can change one element to any other element.
*/
// </vc-description>

// <vc-spec>
method smallest_change(arr: seq<int>) returns (result: int)
  ensures result >= 0
  ensures result <= |arr| / 2
  ensures |arr| == 0 ==> result == 0
  ensures |arr| > 0 ==> result == count_changes_needed(arr, 0, |arr| - 1)
// </vc-spec>
// <vc-code>
{
  if |arr| <= 1 {
    return 0;
  }
  
  count_changes_main_bounded(arr);
  
  var changes := 0;
  var left := 0;
  var right := |arr| - 1;
  
  while left < right
    invariant 0 <= left
    invariant right < |arr|
    invariant left <= right + 1
    invariant changes >= 0
    invariant changes + count_changes_needed(arr, left, right) == count_changes_needed(arr, 0, |arr| - 1)
    decreases right - left
  {
    if arr[left] != arr[right] {
      changes := changes + 1;
    }
    left := left + 1;
    right := right - 1;
  }
  
  result := changes;
}
// </vc-code>
