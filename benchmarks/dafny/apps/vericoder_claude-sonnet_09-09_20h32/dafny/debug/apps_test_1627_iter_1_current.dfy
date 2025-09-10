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

// <vc-helpers>
function swapAdjacent(arr: seq<int>, i: int, j: int): seq<int>
  requires 0 <= i < j < |arr|
  requires j == i + 1
  ensures |swapAdjacent(arr, i, j)| == |arr|
  ensures multiset(swapAdjacent(arr, i, j)) == multiset(arr)
  ensures swapAdjacent(arr, i, j)[i] == arr[j]
  ensures swapAdjacent(arr, i, j)[j] == arr[i]
  ensures forall k :: 0 <= k < |arr| && k != i && k != j ==> swapAdjacent(arr, i, j)[k] == arr[k]
{
  arr[i := arr[j]][j := arr[i]]
}

lemma multisetPreservedBySwap(arr: seq<int>, i: int, j: int)
  requires 0 <= i < j < |arr|
  requires j == i + 1
  ensures multiset(swapAdjacent(arr, i, j)) == multiset(arr)
{
}

lemma bubbleSortCorrectness(arr: seq<int>)
  requires |arr| >= 1
  ensures exists operations :: ValidOperations(operations, |arr|) && isSorted(applyOperations(arr, operations)) && |operations| <= |arr| * |arr|
{
}

lemma operationsValidityPreserved(ops: seq<(int, int)>, newOp: (int, int), n: int)
  requires ValidOperations(ops, n)
  requires 1 <= newOp.0 <= n && 1 <= newOp.1 <= n && newOp.1 == newOp.0 + 1
  ensures ValidOperations(ops + [newOp], n)
{
}

lemma applyOperationsLength(arr: seq<int>, operations: seq<(int, int)>)
  ensures |applyOperations(arr, operations)| == |arr|
  decreases |operations|
{
  if |operations| == 0 {
  } else {
    var op := operations[0];
    if 1 <= op.0 <= |arr| && 1 <= op.1 <= |arr| && op.1 == op.0 + 1 {
      var newArr := swapAdjacent(arr, op.0 - 1, op.1 - 1);
      applyOperationsLength(newArr, operations[1..]);
    } else {
      applyOperationsLength(arr, operations[1..]);
    }
  }
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
{
  if isSorted(arr) {
    return [];
  }
  
  operations := [];
  var currentArr := arr;
  var iterCount := 0;
  
  while !isSorted(currentArr) && iterCount < 20000
    invariant ValidOperations(operations, n)
    invariant |operations| <= iterCount <= 20000
    invariant multiset(currentArr) == multiset(arr)
    invariant |currentArr| == n
    decreases 20000 - iterCount
  {
    var i := 0;
    var swapped := false;
    
    while i < n - 1 && iterCount < 20000
      invariant ValidOperations(operations, n)
      invariant |operations| <= iterCount <= 20000
      invariant multiset(currentArr) == multiset(arr)
      invariant |currentArr| == n
      invariant 0 <= i <= n - 1
      decreases 20000 - iterCount
    {
      if currentArr[i] > currentArr[i + 1] {
        applyOperationsLength(currentArr, [(i + 1, i + 2)]);
        currentArr := swapAdjacent(currentArr, i, i + 1);
        operations := operations + [(i + 1, i + 2)];
        swapped := true;
        iterCount := iterCount + 1;
      }
      i := i + 1;
    }
    
    if !swapped {
      break;
    }
    
    iterCount := iterCount + 1;
  }
}
// </vc-code>

