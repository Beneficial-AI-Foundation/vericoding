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
lemma StateStep(a: seq<int>, m: int, day: int)
  requires m >= 1
  requires 0 <= day < |a|
  ensures ComputeStateAt(a, m, day + 1) == (ComputeStateAt(a, m, day) + a[day]) % m
{
  // The equality follows directly from the definition of ComputeStateAt for day >= 0 and day < |a|
  assert ComputeStateAt(a, m, day + 1) == (ComputeStateAt(a, m, day) + a[day]) % m;
}

lemma PageTurnCorrect(a: seq<int>, m: int, i: int)
  requires m >= 1
  requires 0 <= i < |a|
  ensures ComputePageTurns(a, m, i, ComputeStateAt(a, m, i)) == (ComputeStateAt(a, m, i) + a[i]) / m
{
  // By definition of ComputePageTurns when i < |a|
  assert ComputePageTurns(a, m, i, ComputeStateAt(a, m, i)) == (ComputeStateAt(a, m, i) + a[i]) / m;
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
    // compute page turns for day i using current state s
    var turns := (s + a[i]) / m;
    res[i] := turns;
    // update state to day i+1
    s := (s + a[i]) % m;
    // s now equals ComputeStateAt(a,m,i+1) by lemma
    calc {
      s;
      == { StateStep(a, m, i); }
      ComputeStateAt(a, m, i + 1);
    }
    i := i + 1;
  }
  result := res[..];
}
// </vc-code>

