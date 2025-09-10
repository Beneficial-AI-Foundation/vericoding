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
function PrefixCount(aa: seq<int>, t: int, boss: int): int
  decreases t
{
  if t == 0 then 0 else PrefixCount(aa, t-1, boss) + (if aa[t-1] == boss then 1 else 0)
}

lemma PrefixCount_spec(aa: seq<int>, t: int, boss: int)
  requires 0 <= t <= |aa|
  free ensures PrefixCount(aa, t, boss) == |set j | 0 <= j < t && aa[j] == boss|
  decreases t
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, aa: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, aa)
    ensures ValidOutput(n, aa, result)
// </vc-spec>
// <vc-code>
{
  var res := new int[n](_ => 0);
  assert forall k :: 0 <= k < n ==> res[k] == 0;

  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> res[k] == PrefixCount(aa, |aa|, k+1)
    invariant forall k :: i <= k < n ==> res[k] >= 0
  {
    var cnt := 0;
    var t := 0;
    while t < |aa|
      invariant 0 <= t <= |aa|
      invariant 0 <= cnt
      invariant cnt == PrefixCount(aa, t, i+1)
    {
      if aa[t] == i+1 {
        cnt := cnt + 1;
      }
      t := t + 1;
    }
    res[i] := cnt;
    i := i + 1;
  }

  // Bridge PrefixCount to SubordinateCount for each entry
  var k := 0;
  while k < n
    invariant 0 <= k <= n
  {
    assert res[k] == PrefixCount(aa, |aa|, k+1);
    PrefixCount_spec(aa, |aa|, k+1);
    assert res[k] == SubordinateCount(aa, k+1);
    k := k + 1;
  }

  result := res[..];
}
// </vc-code>

