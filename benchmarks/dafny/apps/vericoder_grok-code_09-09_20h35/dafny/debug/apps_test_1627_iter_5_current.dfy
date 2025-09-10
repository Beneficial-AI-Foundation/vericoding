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

function swapAdjacent(s: seq<int>, i: nat, j: nat): seq<int>
  requires 0 <= i < j < |s|
  ensures |swapAdjacent(s, i, j)| == |s|
  ensures multiset(swapAdjacent(s, i, j)) == multiset(s)
  ensures forall k :: 0 <= k < |s| && k != i && k != j ==> swapAdjacent(s, i, j)[k] == s[k]
  ensures swapAdjacent(s, i, j)[i] == s[j] && swapAdjacent(s, i, j)[j] == s[i]
{
  s[..i] + [s[j], s[i]] + s[j+1..]
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
  } else {
    var a := new int[n];
    forall i | 0 <= i < n { a[i] := arr[i]; }
    var ops: seq<(int, int)> := [];
    var swapped := true;
    while swapped && |ops| < 20000
      invariant |ops| <= 20000
      invariant multiset(arr) == multiset(a[..])
      invariant ValidOperations(ops, n)
    {
      swapped := false;
      var i := 0;
      while i < n - 1 && |ops| < 20000
        invariant 0 <= i <= n - 1
        invariant |ops| <= 20000
        invariant multiset(arr) == multiset(a[..])
        invariant ValidOperations(ops, n)
      {
        if a[i] > a[i + 1] {
          if |ops| < 20000 {
            a[i], a[i + 1] := a[i + 1], a[i];
            ops := ops + [(i + 1, i + 2)];
            swapped := true;
          }
        }
        i := i + 1;
      }
    }
    return ops;
  }
}
// </vc-code>

