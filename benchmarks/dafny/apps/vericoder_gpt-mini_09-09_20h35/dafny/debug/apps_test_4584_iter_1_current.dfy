predicate ValidInput(n: int, aa: seq<int>)
{
    n >= 2 &&
    |aa| == n - 1 &&
    forall i :: 0 <= i < |aa| ==> 1 <= aa[i] < i + 2
}

function SubordinateCount(aa: seq<int>, boss_id: int): int
{
    |set j | 0 <= j < |aa| && aa[j] == boss_id|
}

predicate ValidOutput(n: int, aa: seq<int>, result: seq<int>)
{
    |result| == n &&
    forall i :: 0 <= i < n ==> result[i] >= 0 &&
    forall i :: 0 <= i < n ==> result[i] == SubordinateCount(aa, i + 1)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
{
  var res := new int[n];
  var j := 0;
  while j < |aa|
    invariant 0 <= j <= |aa|
    invariant forall k :: 0 <= k < n ==> res[k] >= 0
    invariant forall k :: 0 <= k < n ==> res[k] == |set t | 0 <= t < j && aa[t] == k+1|
  {
    var b := aa[j];
    // bounds for b: from ValidInput we have 1 <= aa[j] < j+2, and j < |aa| = n-1, so b-1 is a valid index into res
    assert 1 <= b < n;
    // update count for boss b (index b-1)
    res[b-1] := res[b-1] + 1;
    // show invariant holds for j+1:
    // for k != b-1 unchanged; for k == b-1 we incremented because aa[j] == b
    j := j + 1;
  }
  result := res[..];
}
// </vc-code>

