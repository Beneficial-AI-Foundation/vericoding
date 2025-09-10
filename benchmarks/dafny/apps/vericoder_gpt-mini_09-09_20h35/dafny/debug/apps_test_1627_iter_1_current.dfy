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
  requires 0 <= i < |arr|
  requires 0 <= j < |arr|
  requires j == i + 1
  ensures |result| == |arr|
  ensures multiset(result) == multiset(arr)
  ensures forall k :: 0 <= k < |arr| && k != i && k != j ==> result[k] == arr[k]
  ensures result[i] == arr[j] && result[j] == arr[i]
{
  arr[..i] + [arr[j]] + arr[i+1..j] + [arr[i]] + arr[j+1..]
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

  var a := arr;
  var ops := [] : seq<(int, int)>;
  var cap := 20000;
  var cnt := 0;
  var pass := 0;
  while pass < n && cnt < cap && !isSorted(a)
    decreases n - pass
    invariant 0 <= pass <= n
    invariant 0 <= cnt <= cap
    invariant |ops| == cnt
    invariant |a| == n
    invariant multiset(a) == multiset(arr)
    invariant forall op :: op in ops ==> 1 <= op.0 <= n && 1 <= op.1 <= n && op.1 == op.0 + 1
  {
    var k := 0;
    while k < n - 1 && cnt < cap
      decreases n - k
      invariant 0 <= k <= n - 1
      invariant 0 <= cnt <= cap
      invariant |ops| == cnt
      invariant |a| == n
      invariant multiset(a) == multiset(arr)
      invariant forall op :: op in ops ==> 1 <= op.0 <= n && 1 <= op.1 <= n && op.1 == op.0 + 1
    {
      if a[k] > a[k+1] {
        a := swapAdjacent(a, k, k+1);
        ops := ops + [(k+1, k+2)];
        cnt := cnt + 1;
      }
      k := k + 1;
    }
    pass := pass + 1;
  }

  operations := ops;
}
// </vc-code>

