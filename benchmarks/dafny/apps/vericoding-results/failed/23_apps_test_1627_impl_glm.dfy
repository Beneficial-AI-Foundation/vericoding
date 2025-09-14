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
  requires 0 <= i < j < |arr| && j == i + 1
  ensures multiset(swapAdjacent(arr, i, j)) == multiset(arr)
  ensures |swapAdjacent(arr, i, j)| == |arr|
  ensures var result := swapAdjacent(arr, i, j); 
      forall k :: 0 <= k < |result| ==> (k != i && k != j ==> result[k] == arr[k])
  ensures swapAdjacent(arr, i, j)[i] == arr[j]
  ensures swapAdjacent(arr, i, j)[j] == arr[i]
{
  let temp := arr[i] in arr[i := arr[j]][j := temp]
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
  var currentArr := arr;
  var ops := [];
  var n := |currentArr|;
  var lastUnsorted := n - 1;
  
  while lastUnsorted > 0 && |ops| < 20000
    decreases lastUnsorted
    invariant 0 <= lastUnsorted <= n - 1
    invariant |ops| <= 20000
    invariant multiset(currentArr) == multiset(arr)
  {
    var i := 0;
    while i < lastUnsorted
      invariant 0 <= i <= lastUnsorted
      invariant |ops| <= 20000
      invariant multiset(currentArr) == multiset(arr)
      decreases lastUnsorted - i
    {
      if currentArr[i] > currentArr[i+1] {
        currentArr := swapAdjacent(currentArr, i, i+1);
        ops := ops + [(i+1, i+2)];
        if |ops| >= 20000 {
          break;
        }
      }
      i := i + 1;
    }
    lastUnsorted := lastUnsorted - 1;
  }
  return ops;
}
// </vc-code>

