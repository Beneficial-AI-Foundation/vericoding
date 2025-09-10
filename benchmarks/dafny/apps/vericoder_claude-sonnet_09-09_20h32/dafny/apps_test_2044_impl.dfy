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
lemma ComputeStateAtInductive(a: seq<int>, m: int, day: int)
    requires m >= 1
    requires day >= 0
    requires day < |a|
    ensures ComputeStateAt(a, m, day + 1) == (ComputeStateAt(a, m, day) + a[day]) % m
{
}

lemma ComputeStateAtBounds(a: seq<int>, m: int, day: int)
    requires m >= 1
    requires day >= 0
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    ensures 0 <= ComputeStateAt(a, m, day) < m
{
    if day == 0 {
    } else if day > |a| {
        ComputeStateAtBounds(a, m, |a|);
    } else {
        ComputeStateAtBounds(a, m, day - 1);
    }
}

lemma IterativeStateCorrectness(a: seq<int>, m: int, states: seq<int>, i: int)
    requires m >= 1
    requires 0 <= i <= |a|
    requires |states| == i + 1
    requires states[0] == 0
    requires forall j :: 0 <= j < i ==> states[j + 1] == (states[j] + a[j]) % m
    ensures forall j :: 0 <= j <= i ==> states[j] == ComputeStateAt(a, m, j)
{
    if i == 0 {
    } else {
        IterativeStateCorrectness(a, m, states[..i], i - 1);
        ComputeStateAtInductive(a, m, i - 1);
    }
}

lemma DivisionNonNegative(a: int, b: int)
    requires b > 0
    requires a >= 0
    ensures a / b >= 0
{
}

lemma LoopInvariantMaintained(a: seq<int>, m: int, i: int, states: seq<int>)
    requires m >= 1
    requires 0 <= i < |a|
    requires |states| == i + 1
    requires states[0] == 0
    requires forall j :: 0 <= j < i ==> states[j + 1] == (states[j] + a[j]) % m
    requires forall j :: 0 <= j <= i ==> states[j] == ComputeStateAt(a, m, j)
    requires forall k :: 0 <= k < |a| ==> a[k] >= 1
    ensures states[i] == ComputeStateAt(a, m, i)
{
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
    result := [];
    var s := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant s == ComputeStateAt(a, m, i)
        invariant forall j :: 0 <= j < i ==> result[j] == (ComputeStateAt(a, m, j) + a[j]) / m
        invariant forall j :: 0 <= j < i ==> result[j] >= 0
    {
        var page_turns := (s + a[i]) / m;
        result := result + [page_turns];
        s := (s + a[i]) % m;
        i := i + 1;
    }
}
// </vc-code>

