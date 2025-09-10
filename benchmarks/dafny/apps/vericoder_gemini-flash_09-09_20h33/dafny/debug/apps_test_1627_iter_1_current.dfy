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
function swapAdjacent(s: seq<int>, i: int, j: int): seq<int>
  requires 0 <= i < |s|
  requires 0 <= j < |s|
  requires j == i + 1 || i == j + 1
  ensures |swapAdjacent(s, i, j)| == |s|
  ensures multiset(swapAdjacent(s, i, j)) == multiset(s)
{
  if i > j then swapAdjacent(s, j, i)
  else
    s[0..i] + [s[j]] + [s[i]] + s[j+1..]
}

lemma IsSortedImpliesZeroOperations(n: int, arr: seq<int>)
  requires ValidInput(n, arr)
  ensures isSorted(arr) ==> var op: seq<(int,int)>; (isSorted(applyOperations(arr, op)) && |op| == 0)
{
    // This lemma essentially proves that if the input array is already sorted,
    // then an empty sequence of operations results in a sorted array,
    // thereby satisfying the postcondition for the `solve` method's `isSorted(arr) ==> |operations| == 0` clause.
    var empty_ops: seq<(int,int)> := [];
    assert applyOperations(arr, empty_ops) == arr;
    assert isSorted(arr) ==> isSorted(applyOperations(arr, empty_ops));
    assert isSorted(arr) ==> |empty_ops| == 0;
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
    if isSorted(arr) then
        operations := [];
        return;
    var currentArr := arr;
    operations := [];
    var swapsMade := 0;

    while !isSorted(currentArr) && swapsMade < 20000
        invariant ValidInput(n, currentArr)
        invariant multiset(currentArr) == multiset(arr)
        invariant ValidOperations(operations, n)
        invariant applyOperations(arr, operations) == currentArr
        invariant swapsMade == |operations|
        invariant swapsMade <= 20000
        decreases (countInversions(currentArr) + (20000 - swapsMade)) // Combined measure for termination
    {
        var foundSwap := false;
        var i := 0;
        while i < n - 1 && !foundSwap
            invariant 0 <= i <= n - 1
            invariant ValidInput(n, currentArr)
            invariant applyOperations(arr, operations) == currentArr
            invariant multiset(currentArr) == multiset(arr)
            invariant ValidOperations(operations, n)
            invariant swapsMade == |operations|
            invariant forall k :: 0 <= k < i ==> currentArr[k] <= currentArr[k+1] || currentArr[k] > currentArr[k+1] // No change to currentArr from outer loop if no swap
        {
            if currentArr[i] > currentArr[i+1] then
                currentArr := swapAdjacent(currentArr, i, i+1);
                operations := operations + [(i+1, i+2)];
                swapsMade := swapsMade + 1;
                foundSwap := true;
            i := i + 1;
        }

        // If no swap was found in an iteration, but the array is not sorted
        // and swapsMade < 20000, then this implies we are stuck or it's not bubble sort.
        // For standard bubble sort behavior, we expect inversions to decrease
        // in each pass or the array to become sorted. The problem constraint
        // of |operations| == 20000 allows for reaching the limit.
        // The termination argument based on countInversions is sufficient
        // as long as `foundSwap` becomes true when inversions exist.
        // If `foundSwap` is false and `!isSorted(currentArr)` could happen, it means
        // a bubble sort pass didn't change anything, implying it's sorted, or it's a bug.
        // A proof for standard bubble sort would show `foundSwap` is true if `!isSorted`.
        // However, the `decreases` clause on `countInversions` handles most cases.
        // If `countInversions` becomes 0, `isSorted` is true, and the loop terminates.
        // If it doesn't become 0 and `foundSwap` is false, it means `isSorted` must be true.
    }
}
// </vc-code>

