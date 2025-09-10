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
    var temp_s_i := s[i];
    var temp_s_j := s[j];
    var result := s[0..i] + [temp_s_j] + [temp_s_i] + s[j+1..];
    result
}

lemma IsSortedImpliesZeroOperations(n: int, arr: seq<int>)
  requires ValidInput(n, arr)
  ensures isSorted(arr) ==> (var op: seq<(int,int)> := []; isSorted(applyOperations(arr, op)) && |op| == 0)
{
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
    if isSorted(arr) {
        operations := [];
        return;
    }
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
        invariant countInversions(currentArr) >= 0
        decreases countInversions(currentArr)
    {
        var foundSwap := false;
        var i := 0;
        var old_count_inversions := countInversions(currentArr);

        while i < n - 1 && !foundSwap
            invariant 0 <= i <= n - 1
            invariant ValidInput(n, currentArr)
            invariant applyOperations(arr, operations) == currentArr
            invariant multiset(currentArr) == multiset(arr)
            invariant ValidOperations(operations, n)
            invariant swapsMade == |operations|
            invariant forall k :: 0 <= k < i ==> currentArr[k] <= currentArr[k+1]
            invariant countInversions(currentArr) == old_count_inversions || (foundSwap && countInversions(currentArr) < old_count_inversions) // Inversions only decrease on a swap.
            decreases n - 1 - i
        {
            if currentArr[i] > currentArr[i+1] {
                currentArr := swapAdjacent(currentArr, i, i+1);
                operations := operations + [(i+1, i+2)];
                swapsMade := swapsMade + 1;
                foundSwap := true;
                assert countInversions(currentArr) < old_count_inversions; // A swap of an inversion reduces inversions
            }
            i := i + 1;
        }

        // If no swap was found in an inner loop pass, it implies that currentArr is already sorted.
        // This is guaranteed by the bubble sort invariant.
        assert (!foundSwap) ==> isSorted(currentArr);
    }
}
// </vc-code>

