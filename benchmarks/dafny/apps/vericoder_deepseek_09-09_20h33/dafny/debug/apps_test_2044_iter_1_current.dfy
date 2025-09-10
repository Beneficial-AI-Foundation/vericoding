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
lemma ComputeStateAtLemma(a: seq<int>, m: int, day: int, s: int, i: int)
    requires m >= 1
    requires day >= 0
    requires i >= 0 && i <= day
    requires day <= |a|
    requires s == ComputeStateAt(a, m, i)
    ensures ComputeStateAt(a, m, day) == ComputeNextState(a, m, i, ComputeStateAt(a, m, i))
    decreases day - i
{
    if i < day {
        ComputeStateAtLemma(a, m, day - 1, s, i);
        assert ComputeStateAt(a, m, day) == (ComputeStateAt(a, m, day - 1) + a[day - 1]) % m;
        assert ComputeNextState(a, m, day - 1, ComputeStateAt(a, m, day - 1)) == (ComputeStateAt(a, m, day - 1) + a[day - 1]) % m;
    }
}

lemma ComputeStateAtInRange(a: seq<int>, m: int, day: int)
    requires m >= 1
    requires day >= 0
    requires day <= |a|
    ensures 0 <= ComputeStateAt(a, m, day) < m
    decreases day
{
    if day > 0 {
        ComputeStateAtInRange(a, m, day - 1);
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
    result := [];
    var s := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant s == ComputeStateAt(a, m, i)
        invariant ValidOutput(result, i)
        invariant forall j :: 0 <= j < i ==> result[j] == ComputePageTurns(a, m, j, ComputeStateAt(a, m, j))
    {
        var turns := (s + a[i]) / m;
        result := result + [turns];
        s := (s + a[i]) % m;
        i := i + 1;
        
        ComputeStateAtInRange(a, m, i);
        ComputeStateAtLemma(a, m, i, s, i-1);
    }
}
// </vc-code>

