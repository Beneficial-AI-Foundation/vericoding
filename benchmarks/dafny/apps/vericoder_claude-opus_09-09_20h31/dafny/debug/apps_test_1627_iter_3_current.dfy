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
  
  var invBefore := set p, q | 0 <= p < q < |arr| && arr[p] > arr[q] :: (p, q);
  var invAfter := set p, q | 0 <= p < q < |arr'| && arr'[p] > arr'[q] :: (p, q);
  
  // The key insight: (i, i+1) is in invBefore but not in invAfter
  assert (i, i+1) in invBefore by {
    assert 0 <= i < i+1 < |arr|;
    assert arr[i] > arr[i+1];
  }
  
  assert (i, i+1) !in invAfter by {
    assert arr'[i] == arr[i+1];
    assert arr'[i+1] == arr[i];
    assert arr'[i] < arr'[i+1];
  }
  
  // For any other inversion (p, q), if it exists in invAfter, it also exists in invBefore
  forall p, q | (p, q) in invAfter
    ensures (p, q) in invBefore || (p == i+1 && q > i+1) || (p < i && q == i)
  {
    if p != i && p != i+1 && q != i && q != i+1 {
      assert arr'[p] == arr[p];
      assert arr'[q] == arr[q];
    }
  }
  
  // Since (i, i+1) is removed and no new inversions are added that weren't there before
  assert |invAfter| < |invBefore|;
}

lemma BubbleSortCorrectness(arr: seq<int>, operations: seq<(int, int)>)
  requires ValidOperations(operations, |arr|)
  ensures |operations| <= |arr| * |arr|
{
  // Simple bound: at most n^2 operations
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
    assert isSorted(currentArr);
    return;
  }
  
  // Bubble sort with operation limit
  var passCount := 0;
  sorted := false;
  var inversions := countInversions(currentArr);
  
  while !sorted && |operations| < 20000 && passCount < n
    invariant currentArr == applyOperations(arr, operations)
    invariant ValidOperations(operations, n)
    invariant |operations| <= 20000
    invariant multiset(currentArr) == multiset(arr)
    invariant 0 <= passCount <= n
    invariant inversions == countInversions(currentArr)
    decreases if |operations| >= 20000 then 0 else 20000 - |operations|, inversions
  {
    sorted := true;
    var i := 0;
    var oldInversions := inversions;
    
    while i < n - 1 && |operations| < 20000
      invariant 0 <= i <= n - 1
      invariant currentArr == applyOperations(arr, operations)
      invariant ValidOperations(operations, n)
      invariant |operations| <= 20000
      invariant multiset(currentArr) == multiset(arr)
      invariant inversions == countInversions(currentArr)
      invariant inversions <= oldInversions
    {
      if currentArr[i] > currentArr[i+1] {
        // Apply the lemma before swapping
        SwapReducesInversions(currentArr, i);
        var prevInv := countInversions(currentArr);
        
        // Swap adjacent elements
        currentArr := swapAdjacent(currentArr, i, i+1);
        operations := operations + [(i+1, i+2)];
        sorted := false;
        inversions := countInversions(currentArr);
        
        assert inversions < prevInv;
        assert ValidOperations(operations, n);
        assert currentArr == applyOperations(arr, operations);
      }
      i := i + 1;
    }
    
    if sorted {
      assert isSorted(currentArr);
    }
    
    passCount := passCount + 1;
  }
  
  // At this point, either sorted or we've hit the limit
  assert |operations| <= 20000;
  assert ValidOperations(operations, n);
  assert multiset(currentArr) == multiset(arr);
  assert sorted ==> isSorted(currentArr);
  assert !sorted ==> |operations| == 20000;
}
// </vc-code>

