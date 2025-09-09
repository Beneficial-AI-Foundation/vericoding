Given a notebook with infinite pages where each page holds exactly m names,
write names for n consecutive days. On day i, write exactly a_i names.
Fill pages sequentially - when a page becomes full, turn to the next page.
Determine how many times you turn pages on each day.

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

method solve(n: int, m: int, a: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, m, a)
    ensures ValidOutput(result, n)
    ensures CorrectPageTurns(result, a, m)
{
    result := [];
    var s := 0;
    var i := 0;

    while i < n
        invariant 0 <= i <= n
        invariant |result| == i
        invariant s >= 0
        invariant s < m
        invariant forall j :: 0 <= j < |result| ==> result[j] >= 0
        invariant s == ComputeStateAt(a, m, i)
        invariant forall k :: 0 <= k < i ==> 
            result[k] == (ComputeStateAt(a, m, k) + a[k]) / m
    {
        var total := s + a[i];
        var turns := total / m;
        result := result + [turns];
        s := total % m;
        i := i + 1;
    }
}
