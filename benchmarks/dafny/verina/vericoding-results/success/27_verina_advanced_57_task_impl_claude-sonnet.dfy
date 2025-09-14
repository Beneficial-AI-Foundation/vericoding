// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed reads clauses from lemmas as they are not allowed */
function FindInArray(arr: array<int>, target: int): int
  reads arr
{
  if arr.Length == 0 then -1
  else
    FindInArrayHelper(arr, target, 0)
}

function FindInArrayHelper(arr: array<int>, target: int, index: int): int
  reads arr
  requires 0 <= index <= arr.Length
  decreases arr.Length - index
{
  if index >= arr.Length then -1
  else if arr[index] == target then index
  else FindInArrayHelper(arr, target, index + 1)
}

function FindNextGreater(arr: array<int>, startIndex: int): int
  reads arr
  requires 0 <= startIndex < arr.Length
{
  FindNextGreaterHelper(arr, startIndex, startIndex + 1)
}

function FindNextGreaterHelper(arr: array<int>, startIndex: int, currentIndex: int): int
  reads arr
  requires 0 <= startIndex < arr.Length
  requires startIndex < currentIndex <= arr.Length
  decreases arr.Length - currentIndex
{
  if currentIndex >= arr.Length then -1
  else if arr[currentIndex] > arr[startIndex] then arr[currentIndex]
  else FindNextGreaterHelper(arr, startIndex, currentIndex + 1)
}

lemma FindInArrayValid(arr: array<int>, target: int)
  ensures var idx := FindInArray(arr, target); idx == -1 || (0 <= idx < arr.Length && arr[idx] == target)
{
  if arr.Length > 0 {
    FindInArrayHelperValid(arr, target, 0);
  }
}

lemma FindInArrayHelperValid(arr: array<int>, target: int, index: int)
  requires 0 <= index <= arr.Length
  ensures var idx := FindInArrayHelper(arr, target, index); idx == -1 || (index <= idx < arr.Length && arr[idx] == target)
  decreases arr.Length - index
{
  if index < arr.Length && arr[index] != target {
    FindInArrayHelperValid(arr, target, index + 1);
  }
}
// </vc-helpers>

// <vc-spec>
method NextGreaterElement(nums1: array<int>, nums2: array<int>) returns (result: array<int>)
    requires
        forall i, j :: 0 <= i < nums1.Length && 0 <= j < nums1.Length && i != j ==> nums1[i] != nums1[j]
    requires
        forall i, j :: 0 <= i < nums2.Length && 0 <= j < nums2.Length && i != j ==> nums2[i] != nums2[j]
    ensures
        result.Length == nums1.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Added validation to ensure targetIndex is valid before calling FindNextGreater */
  result := new int[nums1.Length];
  
  var i := 0;
  while i < nums1.Length
    invariant 0 <= i <= nums1.Length
    invariant result.Length == nums1.Length
  {
    FindInArrayValid(nums2, nums1[i]);
    var targetIndex := FindInArray(nums2, nums1[i]);
    if targetIndex >= 0 && targetIndex < nums2.Length {
      result[i] := FindNextGreater(nums2, targetIndex);
    } else {
      result[i] := -1;
    }
    i := i + 1;
  }
}
// </vc-code>
