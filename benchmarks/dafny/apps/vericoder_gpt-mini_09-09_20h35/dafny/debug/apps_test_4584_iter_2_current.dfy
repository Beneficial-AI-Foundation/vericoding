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
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
{
  var res := new int[n];
  // initial zeros
  assert forall k :: 0 <= k < n ==> res[k] == 0;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> res[k] == |set t | 0 <= t < |aa| && aa[t] == k+1|
    invariant forall k :: i <= k < n ==> res[k] >= 0
  {
    var cnt := 0;
    var t := 0;
    while t < |aa|
      invariant 0 <= t <= |aa|
      invariant 0 <= cnt
      invariant cnt == |set j | 0 <= j < t && aa[j] == i+1|
    {
      if aa[t] == i+1 {
        cnt := cnt + 1;
      }
      t := t + 1;
    }
    // cnt now equals total occurrences of i+1 in aa
    res[i] := cnt;
    i := i + 1;
  }
  result := res[..];
}
// </vc-code>

