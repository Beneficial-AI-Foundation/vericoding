predicate ValidInput(n: int, m: int, a: seq<int>)
{
    n >= 1 && m >= 1 && |a| == n && 
    (forall i :: 0 <= i < |a| ==> a[i] >= 1)
}

predicate ValidOutput(result: seq<int>, n: int)
{
    |result| == n && (forall i :: 0 <= i < |result| ==> result[i] >= 0)
}

function ComputePageTurns(a: seq<int>, m: int, i: int, s: int): int
    requires m >= 1
    requires i >= 0
    requires s >= 0
{
    if i >= |a| then 0
    else (s + a[i]) / m
}

function ComputeNextState(a: seq<int>, m: int, i: int, s: int): int
    requires m >= 1
    requires i >= 0
    requires s >= 0
{
    if i >= |a| then s
    else (s + a[i]) % m
}

predicate CorrectPageTurns(result: seq<int>, a: seq<int>, m: int)
    requires m >= 1
{
    |result| == |a| &&
    (forall i :: 0 <= i < |a| ==> 
        var s := ComputeStateAt(a, m, i);
        result[i] == (s + a[i]) / m)
}

function ComputeStateAt(a: seq<int>, m: int, day: int): int
    requires m >= 1
    requires day >= 0
{
    if day == 0 then 0
    else if day > |a| then ComputeStateAt(a, m, |a|)
    else (ComputeStateAt(a, m, day - 1) + a[day - 1]) % m
}

// <vc-helpers>
lemma ComputeStateAtRange(a: seq<int>, m: int, day: int)
    requires m >= 1
    requires 0 <= day <= |a|
    ensures 0 <= ComputeStateAt(a, m, day) < m
    decreases day
{
    if day == 0 {
    } else {
        assert 0 <= day - 1 < |a|;
        ComputeStateAtRange(a, m, day - 1);
        assert ComputeStateAt(a, m, day) == (ComputeStateAt(a, m, day - 1) + a[day - 1]) % m;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, a: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, m, a)
    ensures ValidOutput(result, n)
    ensures CorrectPageTurns(result, a, m)
// </vc-spec>
// <vc-code>
{
  var r: seq<int> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |r| == i
    invariant forall j :: 0 <= j < |r| ==> r[j] == (ComputeStateAt(a, m, j) + a[j]) / m
    invariant forall j :: 0 <= j < |r| ==> r[j] >= 0
  {
    assert n == |a|;
    assert i < |a|;
    ComputeStateAtRange(a, m, i);
    assert 0 <= ComputeStateAt(a, m, i) < m;
    assert a[i] >= 1;
    var v := (ComputeStateAt(a, m, i) + a[i]) / m;
    var r0 := r;
    // capture invariants for r0 (the old r)
    assert forall j :: 0 <= j < |r0| ==> r0[j] == (ComputeStateAt(a, m, j) + a[j]) / m;
    assert forall j :: 0 <= j < |r0| ==> r0[j] >= 0;

    r := r0 + [v];
    assert |r| == |r0| + 1;
    assert |r0| == i;

    // Maintain the functional invariant
    assert forall j :: 0 <= j < |r| ==> r[j] == (ComputeStateAt(a, m, j) + a[j]) / m
      by {
        forall j | 0 <= j < |r|
          ensures r[j] == (ComputeStateAt(a, m, j) + a[j]) / m
        {
          if j < |r0| {
            assert r[j] == r0[j];
            assert r0[j] == (ComputeStateAt(a, m, j) + a[j]) / m;
          } else {
            assert j == |r0|;
            assert j == i;
            assert r[j] == v;
            assert v == (ComputeStateAt(a, m, j) + a[j]) / m;
            assert j < |a|;
          }
        }
      }

    // Maintain non-negativity
    assert forall j :: 0 <= j < |r| ==> r[j] >= 0
      by {
        forall j | 0 <= j < |r|
          ensures r[j] >= 0
        {
          if j < |r0| {
            assert r[j] == r0[j];
            assert r[j] >= 0;
          } else {
            assert j == |r0|;
            assert j == i;
            assert r[j] == v;
            assert j < |a|;
            assert v == (ComputeStateAt(a, m, j) + a[j]) / m;
            assert (ComputeStateAt(a, m, j) + a[j]) >= 1;
            assert m >= 1;
          }
        }
      }
    i := i + 1;
  }
  result := r;

  // ValidOutput(result, n)
  assert |result| == n;
  assert forall i :: 0 <= i < |result| ==> result[i] >= 0;

  // CorrectPageTurns(result, a, m)
  assert |result| == |a|;
  assert forall k :: 0 <= k < |a| ==> result[k] == (ComputeStateAt(a, m, k) + a[k]) / m
  by {
    forall k | 0 <= k < |a|
      ensures result[k] == (ComputeStateAt(a, m, k) + a[k]) / m
    {
      assert k < |result|;
      assert result[k] == (ComputeStateAt(a, m, k) + a[k]) / m;
    }
  }
}
// </vc-code>

