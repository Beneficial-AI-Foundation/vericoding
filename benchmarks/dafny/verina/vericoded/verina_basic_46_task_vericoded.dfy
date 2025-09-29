// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Added 'reads arr' clause to fix compilation error */
function BinarySearchLast(arr: array<int>, elem: int, left: int, right: int): int
  reads arr
  requires 0 <= left <= right + 1 <= arr.Length
  requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
  ensures -1 <= BinarySearchLast(arr, elem, left, right) <= right
  ensures BinarySearchLast(arr, elem, left, right) >= 0 ==>
    left <= BinarySearchLast(arr, elem, left, right) <= right &&
    arr[BinarySearchLast(arr, elem, left, right)] == elem &&
    (BinarySearchLast(arr, elem, left, right) < right ==> arr[BinarySearchLast(arr, elem, left, right) + 1] > elem)
  ensures BinarySearchLast(arr, elem, left, right) == -1 ==>
    forall k :: left <= k <= right ==> arr[k] != elem
  decreases right - left + 1
{
  if left > right then
    -1
  else if left == right then
    if arr[left] == elem then left else -1
  else
    var mid := left + (right - left) / 2;
    if arr[mid] == elem then
      if mid < right && arr[mid + 1] == elem then
        BinarySearchLast(arr, elem, mid + 1, right)
      else
        mid
    else if arr[mid] < elem then
      BinarySearchLast(arr, elem, mid + 1, right)
    else
      BinarySearchLast(arr, elem, left, mid - 1)
}
// </vc-helpers>

// <vc-spec>
method LastPosition(arr: array<int>, elem: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < arr.Length ==> arr[i] <= arr[j]
    ensures
        (result >= 0 ==> 
            0 <= result < arr.Length &&
            arr[result] == elem &&
            forall k :: result < k < arr.Length ==> arr[k] != elem) &&
        (result == -1 ==> forall k :: 0 <= k < arr.Length ==> arr[k] != elem)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): No changes needed, just calling the fixed helper */
  if arr.Length == 0 {
    result := -1;
  } else {
    result := BinarySearchLast(arr, elem, 0, arr.Length - 1);
  }
}
// </vc-code>
