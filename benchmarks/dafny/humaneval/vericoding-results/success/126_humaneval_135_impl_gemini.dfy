// <vc-preamble>

predicate ValidInput(arr: seq<int>) {
    forall i, j :: 0 <= i < j < |arr| ==> arr[i] != arr[j]
}

predicate HasDecreaseAt(arr: seq<int>, i: int) {
    1 <= i < |arr| && arr[i] < arr[i-1]
}

predicate IsLargestDecreaseIndex(arr: seq<int>, result: int) {
    HasDecreaseAt(arr, result) && 
    (forall j :: result < j < |arr| ==> arr[j] >= arr[j-1])
}

predicate IsNonDecreasing(arr: seq<int>) {
    forall i :: 1 <= i < |arr| ==> arr[i] >= arr[i-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [fixed index out of range error] */
predicate IsNonDecreasingInPrefix(arr: seq<int>, k: int)
{
    forall i :: 1 <= i <= k && i < |arr| ==> arr[i] >= arr[i-1]
}

/* helper modified by LLM (iteration 2): [fixed index out of range error] */
predicate IsLargestDecreaseIndexInPrefix(arr: seq<int>, result: int, k: int)
{
    HasDecreaseAt(arr, result) && result <= k &&
    (forall j :: result < j <= k && j < |arr| ==> arr[j] >= arr[j-1])
}

function find_last_decrease_recursive(arr: seq<int>, k: int): (res: int)
  requires ValidInput(arr)
  requires 0 <= k < |arr|
  decreases k
  ensures res == -1 || (0 < res <= k)
  ensures (res == -1) <==> IsNonDecreasingInPrefix(arr, k)
  ensures res != -1 ==> IsLargestDecreaseIndexInPrefix(arr, res, k)
{
  if k < 1 then -1
  else if arr[k] < arr[k-1] then k
  else find_last_decrease_recursive(arr, k-1)
}
// </vc-helpers>

// <vc-spec>
method can_arrange(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result == -1 || (0 < result < |arr|)
    ensures result == -1 ==> IsNonDecreasing(arr)
    ensures result != -1 ==> IsLargestDecreaseIndex(arr, result)
    ensures result != -1 ==> (exists i :: HasDecreaseAt(arr, i))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [no changes; logic depends on fixed helpers] */
  if |arr| < 2 {
    result := -1;
  } else {
    result := find_last_decrease_recursive(arr, |arr| - 1);
  }
}
// </vc-code>
