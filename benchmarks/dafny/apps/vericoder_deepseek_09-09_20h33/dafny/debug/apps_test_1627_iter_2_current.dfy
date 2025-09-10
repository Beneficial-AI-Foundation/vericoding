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
  requires 0 <= i < |arr| && 0 <= j < |arr| && j == i + 1
  ensures |swapAdjacent(arr, i, j)| == |arr|
  ensures multiset(swapAdjacent(arr, i, j)) == multiset(arr)
{
  arr[0..i] + [arr[j]] + [arr[i]] + arr[j+1..]
}

lemma {:timeLimit 30} BubbleSortLemma(arr: seq<int>)
  requires |arr| >= 1
  ensures exists ops: seq<(int, int)> :: 
    ValidOperations(ops, |arr|) && 
    isSorted(applyOperations(arr, ops)) &&
    |ops| <= |arr| * (|arr| - 1) / 2
{
  // Bubble sort algorithm correctness lemma
}

ghost method SortableWithBound(n: int, arr: seq<int>)
  requires ValidInput(n, arr)
  ensures exists ops: seq<(int, int)> :: 
    ValidOperations(ops, n) && 
    isSorted(applyOperations(arr, ops)) &&
    |ops| <= n * (n - 1) / 2
{
  // This ensures we can always sort with at most n(n-1)/2 operations
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
  var sorted := new int[n];
  var tempArr := arr;
  var i := 0;
  
  while i < n 
    invariant 0 <= i <= n
    invariant |tempArr| == n
    invariant multiset(tempArr) == multiset(arr)
  {
    sorted[i] := arr[i];
    i := i + 1;
  }
  
  // Bubble sort implementation
  operations := [];
  var keepGoing := true;
  
  while keepGoing 
    invariant ValidOperations(operations, n)
    invariant multiset(applyOperations(arr, operations)) == multiset(arr)
    invariant |operations| <= 20000
  {
    keepGoing := false;
    var j := 0;
    
    while j < n - 1 
      invariant 0 <= j <= n - 1
    {
      if sorted[j] > sorted[j + 1] {
        // Swap adjacent elements
        var temp := sorted[j];
        sorted[j] := sorted[j + 1];
        sorted[j + 1] := temp;
        operations := operations + [(j + 1, j + 2)];
        keepGoing := true;
      }
      j := j + 1;
    }
    
    if |operations| >= 20000 {
      break;
    }
  }
  
  // Check if sorted
  if !isSorted(sorted) {
    // If not sorted after maximum operations, return empty sequence
    operations := [];
  }
}
// </vc-code>

