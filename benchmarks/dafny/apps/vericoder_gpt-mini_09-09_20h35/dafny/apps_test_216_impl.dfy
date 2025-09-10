function sum_abs(arr: seq<int>, i: int): int
    requires 0 <= i <= |arr|
    decreases |arr| - i
{
    if i == |arr| then 0
    else (if arr[i] >= 0 then arr[i] else -arr[i]) + sum_abs(arr, i + 1)
}

predicate ValidInput(n: int, arr: seq<int>)
{
    0 <= n == |arr|
}

// <vc-helpers>
// No helpers required for this proof.
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
    requires ValidInput(n, arr)
    ensures result == sum_abs(arr, 0)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  result := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result + sum_abs(arr, i) == sum_abs(arr, 0)
  {
    var v := arr[i];
    var a := if v >= 0 then v else -v;
    result := result + a;
    i := i + 1;
  }
}
// </vc-code>

