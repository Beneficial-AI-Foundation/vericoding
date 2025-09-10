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
  // The elements involved in the swap are s[i] and s[j].
  // The multiset of the result should be the same as the multiset of the original sequence.
  ensures multiset(swapAdjacent(s, i, j)) == multiset(s)
  // Prove that the multiset property holds by decomposing the sequence and showing
  // that swapping two elements doesn't change the overall multiset.
  decreases 0
{
  if i > j then swapAdjacent(s, j, i)
  else
    // Case where j == i + 1
    // s = s[0..i] + [s[i]] + [s[j]] + s[j+1..]
    // result = s[0..i] + [s[j]] + [s[i]] + s[j+1..]
    var temp_s_i := s[i];
    var temp_s_j := s[j];
    var result := s[0..i] + [temp_s_j] + [temp_s_i] + s[j+1..];

    // Proof sketch for multiset equality:
    // multiset(s) = multiset(s[0..i]) + multiset([s[i]]) + multiset([s[j]]) + multiset(s[j+1..])
    // multiset(result) = multiset(s[0..i]) + multiset([s[j]]) + multiset([s[i]]) + multiset(s[j+1..])
    // Since multiset([s[i]]) + multiset([s[j]]) == multiset([s[j]]) + multiset([s[i]]),
    // the multisets are equal.
    result
}

lemma IsSortedImpliesZeroOperations(n: int, arr: seq<int>)
  requires ValidInput(n, arr)
  ensures isSorted(arr) ==> (var op: seq<(int,int)> := []; isSorted(applyOperations(arr, op)) && |op| == 0)
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
        decreases (countInversions(currentArr), 20000 - swapsMade)
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
            invariant old_count_inversions == countInversions(currentArr) // This must hold before a swap too
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

        // If no swap was found in an inner loop pass, but the array is not sorted
        // and currentArr is not sorted, this means there are no inversions among
        // adjacent elements. However, since the outer loop continues as long as
        // currentArr is not sorted, this guarantees that foundSwap must be true
        // if the iteration actually helps sorting.
        // We need to ensure termination by making progress on `countInversions(currentArr)`
        // or increasing `swapsMade` which is bounded.
        // The bubble sort algorithm guarantees that `foundSwap` will be true
        // as long as the array is not sorted.
        assert currentArr == arr || foundSwap; // Either the array was already sorted or a swap occurred.
    }
}
// </vc-code>

