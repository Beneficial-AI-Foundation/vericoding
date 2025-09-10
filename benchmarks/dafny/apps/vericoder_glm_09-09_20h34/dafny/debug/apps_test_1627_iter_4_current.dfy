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
  ensures |swapAdjacent(arr, i, j)| == |arr|
  ensures multiset(swapAdjacent(arr, i, j)) == multiset(arr)
  ensures forall k :: 0 <= k < |arr| && k != i && k != j ==> swapAdjacent(arr, i, j)[k] == arr[k]
  ensures swapAdjacent(arr, i, j)[i] == arr[j]
  ensures swapAdjacent(arr, i, j)[j] == arr[i]
{
    arr[i := arr[j]][j := arr[i]]
}

function bubbleSortPass(arr: seq<int>, start: int, end: int): (seq<int>, seq<(int, int)>)
  requires 0 <= start <= end <= |arr|
  ensures var (newArr, ops) := bubbleSortPass(arr, start, end);
      |newArr| == |arr| && multiset(newArr) == multiset(arr)
  ensures forall i :: 0 <= i < |arr| && (i < start || i >= end || i == end-1) ==> newArr[i] == arr[i]
  ensures start >= end ==> |ops| == 0 && newArr == arr
  ensures var (newArr, ops) := bubbleSortPass(arr, start, end);
      |ops| <= if start < end then end - start else 0
  decreases end - start
{
  if start >= end then
    (arr, [])
  else
    var next_arr, next_ops := bubbleSortPass(arr, start + 1, end);
    if |next_arr| > start && arr[start] > next_arr[start+1] then
      (swapAdjacent(next_arr, start, start+1), next_ops + [(start+1, start+2)])
    else
      (next_arr, next_ops)
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
  
  ghost var inv := countInversions(arr);
  var current_arr := arr;
  var collected_ops := [];
  var op_count := 0;
  var max_ops := 20000;
  
  while !isSorted(current_arr) && op_count < max_ops
    invariant 0 <= op_count <= max_ops
    invariant op_count <= max_ops
    invariant |collected_ops| == op_count
    invariant |current_arr| == n
    invariant multiset(current_arr) == multiset(arr)
    invariant ValidOperations(collected_ops, n)
    invariant ValidInput(n, current_arr)
    invariant countInversions(current_arr) == inv - op_count
  {
    var new_arr, new_ops := bubbleSortPass(current_arr, 0, n);
    current_arr := new_arr;
    collected_ops := collected_ops + new_ops;
    op_count := op_count + |new_ops|;
  }
  
  return collected_ops;
}
// </vc-code>

