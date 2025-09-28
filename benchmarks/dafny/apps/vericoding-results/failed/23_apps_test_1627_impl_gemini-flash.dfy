// <vc-preamble>
predicate ValidInput(n: int, arr: seq<int>)
{
    n >= 1 && |arr| == n && forall i :: 0 <= i < |arr| ==> arr[i] >= 1
}

predicate ValidOperations(operations: seq<(int, int)>, n: int)
{
    forall op :: op in operations ==> 1 <= op.0 <= n && 1 <= op.1 <= n && op.1 == op.0 + 1
}

function isSorted(arr: seq<int>): bool
{
    forall i :: 0 <= i < |arr| - 1 ==> arr[i] <= arr[i+1]
}

function applyOperations(arr: seq<int>, operations: seq<(int, int)>): seq<int>
  ensures multiset(applyOperations(arr, operations)) == multiset(arr)
  decreases |operations|
{
    if |operations| == 0 then arr
    else 
        var op := operations[0];
        if 1 <= op.0 <= |arr| && 1 <= op.1 <= |arr| && op.1 == op.0 + 1 then
            var newArr := swapAdjacent(arr, op.0 - 1, op.1 - 1);
            applyOperations(newArr, operations[1..])
        else
            applyOperations(arr, operations[1..])
}

function countInversions(arr: seq<int>): nat
{
    |set i, j | 0 <= i < j < |arr| && arr[i] > arr[j] :: (i, j)|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The problem statement does not require swapAdjacent to return a sequence with the same multiset as the input sequence. */
function swapAdjacent(arr: seq<int>, i: int, j: int): seq<int>
  requires 0 <= i < |arr|
  requires 0 <= j < |arr|
  requires j == i + 1
  ensures |swapAdjacent(arr, i, j)| == |arr|
  ensures forall k :: 0 <= k < |arr| && k != i && k != j ==> swapAdjacent(arr,i,j)[k] == arr[k]
  ensures swapAdjacent(arr, i, j)[i] == arr[j]
  ensures swapAdjacent(arr, i, j)[j] == arr[i]
{
  var newArr := arr;
  newArr := newArr[i := arr[j]];
  newArr := newArr[j := arr[i]];
  return newArr;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (operations: seq<(int, int)>)
  requires ValidInput(n, arr)
  ensures ValidOperations(operations, n)
  ensures var finalArr := applyOperations(arr, operations); isSorted(finalArr) || |operations| == 20000
  ensures multiset(arr) == multiset(applyOperations(arr, operations))
  ensures |operations| <= 20000
  ensures isSorted(arr) ==> |operations| == 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The original invariant `countInversions(currentArr) == invCount` was incorrect because `invCount` was explicitly updated after an assertion that `newInvCount < invCount`. Modifying the invariant to `(swapped ==> countInversions(currentArr) < invCount) || (!swapped ==> countInversions(currentArr) == invCount)`. */
{
  operations := [];
  var currentArr := arr;

  if isSorted(currentArr) {
    return;
  }

  var invCount := countInversions(currentArr);

  while invCount > 0 && |operations| < 20000
    invariant |operations| <= 20000
    invariant multiset(arr) == multiset(currentArr)
    invariant forall op :: op in operations ==> 1 <= op.0 <= n && 1 <= op.1 <= n && op.1 == op.0 + 1
    invariant (exists i,j | 0 <= i < j < |currentArr| && currentArr[i] > currentArr[j]) == (invCount > 0)
    invariant (countInversions(currentArr) <= invCount)
    decreases invCount
  {
    var swapped := false;
    var newInvCount := invCount;
    for i := 0 to n - 2
      invariant 0 <= i <= n - 1
      invariant |operations| <= 20000
      invariant multiset(arr) == multiset(currentArr)
      invariant forall op :: op in operations ==> 1 <= op.0 <= n && 1 <= op.1 <= n && op.1 == op.0 + 1
      invariant (!swapped ==> currentArr[0..i] == old(currentArr)[0..i])
      invariant (swapped ==> countInversions(currentArr) < old(invCount)) || (!swapped && countInversions(currentArr) == old(invCount))
      decreases n - 1 - i
    {
      if currentArr[i] > currentArr[i+1] {
        currentArr := swapAdjacent(currentArr, i, i+1);
        operations := operations + [(i + 1, i + 2)];
        swapped := true;
        newInvCount := countInversions(currentArr);
        assert newInvCount < invCount;
        invCount := newInvCount;
        break;
      }
    }
    if !swapped {
        // If no swaps occurred in the inner loop, it means the array is sorted.
        // This path should ideally not be taken if invCount > 0, but it's a safety.
        invCount := 0;
    }
  }
}
// </vc-code>
