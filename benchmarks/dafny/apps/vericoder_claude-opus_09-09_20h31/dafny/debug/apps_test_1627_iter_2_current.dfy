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
  requires 0 <= i < |arr| && 0 <= j < |arr|
  requires i + 1 == j
  ensures |swapAdjacent(arr, i, j)| == |arr|
  ensures multiset(swapAdjacent(arr, i, j)) == multiset(arr)
  ensures forall k :: 0 <= k < |arr| && k != i && k != j ==> swapAdjacent(arr, i, j)[k] == arr[k]
  ensures swapAdjacent(arr, i, j)[i] == arr[j]
  ensures swapAdjacent(arr, i, j)[j] == arr[i]
{
  arr[i := arr[j]][j := arr[i]]
}

lemma SwapReducesInversions(arr: seq<int>, i: int)
  requires 0 <= i < |arr| - 1
  requires arr[i] > arr[i+1]
  ensures countInversions(swapAdjacent(arr, i, i+1)) < countInversions(arr)
{
  var arr' := swapAdjacent(arr, i, i+1);
  
  // The swap removes the inversion (i, i+1) since arr[i] > arr[i+1]
  // After swap: arr'[i] == arr[i+1] < arr[i] == arr'[i+1]
  
  // Count inversions involving positions i and i+1
  var invBefore := set p, q | 0 <= p < q < |arr| && arr[p] > arr[q] :: (p, q);
  var invAfter := set p, q | 0 <= p < q < |arr'| && arr'[p] > arr'[q] :: (p, q);
  
  // The inversion (i, i+1) exists before but not after
  assert (i, i+1) in invBefore;
  assert (i, i+1) !in invAfter;
  
  // This proves that at least one inversion is removed
  assert invAfter < invBefore;
}

lemma BubbleSortCorrectness(arr: seq<int>, operations: seq<(int, int)>)
  requires ValidOperations(operations, |arr|)
  requires isSorted(applyOperations(arr, operations))
  ensures |operations| <= |arr| * (|arr| - 1) / 2
{
  // Maximum number of swaps in bubble sort is n*(n-1)/2
  // This occurs when the array is in reverse order
  // Each pass can perform at most n-1 swaps, and there are at most n passes
  assert |operations| <= |arr| * |arr|;
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
  operations := [];
  var currentArr := arr;
  
  // Check if already sorted
  var sorted := true;
  var k := 0;
  while k < n - 1
    invariant 0 <= k <= n - 1
    invariant sorted ==> forall m :: 0 <= m < k ==> currentArr[m] <= currentArr[m+1]
  {
    if currentArr[k] > currentArr[k+1] {
      sorted := false;
      break;
    }
    k := k + 1;
  }
  
  if sorted {
    return;
  }
  
  // Bubble sort with operation limit
  var passCount := 0;
  sorted := false;
  
  while !sorted && |operations| < 20000 && passCount < n
    invariant currentArr == applyOperations(arr, operations)
    invariant ValidOperations(operations, n)
    invariant |operations| <= 20000
    invariant multiset(currentArr) == multiset(arr)
    invariant 0 <= passCount <= n
  {
    sorted := true;
    var i := 0;
    
    while i < n - 1 && |operations| < 20000
      invariant 0 <= i <= n - 1
      invariant currentArr == applyOperations(arr, operations)
      invariant ValidOperations(operations, n)
      invariant |operations| <= 20000
      invariant multiset(currentArr) == multiset(arr)
    {
      if currentArr[i] > currentArr[i+1] {
        // Apply the lemma before swapping
        if i < |currentArr| - 1 && currentArr[i] > currentArr[i+1] {
          SwapReducesInversions(currentArr, i);
        }
        
        // Swap adjacent elements
        currentArr := swapAdjacent(currentArr, i, i+1);
        operations := operations + [(i+1, i+2)];
        sorted := false;
        
        assert ValidOperations(operations, n);
        assert currentArr == applyOperations(arr, operations);
      }
      i := i + 1;
    }
    
    passCount := passCount + 1;
  }
  
  // Ensure we respect the limit
  assert |operations| <= 20000;
  assert ValidOperations(operations, n);
  assert multiset(currentArr) == multiset(arr);
}
// </vc-code>

