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
lemma ComputeStateAt_step(a: seq<int>, m: int, i: int)
    requires m >= 1
    requires 0 <= i < |a|
    ensures ComputeStateAt(a, m, i + 1) == (ComputeStateAt(a, m, i) + a[i]) % m
{
    // By the definition of ComputeStateAt, when 0 < i+1 <= |a| we have the required equality.
    assert i + 1 <= |a|;
    assert ComputeStateAt(a, m, i + 1) == (ComputeStateAt(a, m, i) + a[i]) % m;
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
  var res := new int[n];
  var s := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s >= 0
    invariant s == ComputeStateAt(a, m, i)
    invariant (forall j :: 0 <= j < i ==> res[j] == (ComputeStateAt(a, m, j) + a[j]) / m)
  {
    var turns := (s + a[i]) / m;
    res[i] := turns;
    ComputeStateAt_step(a, m, i);
    s := (s + a[i]) % m;
    assert s == ComputeStateAt(a, m, i + 1);
    i := i + 1;
  }
  result := res[..];
}
// </vc-code>

