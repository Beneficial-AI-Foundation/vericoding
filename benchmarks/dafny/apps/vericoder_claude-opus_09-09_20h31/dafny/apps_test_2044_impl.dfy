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
    requires 0 <= day <= |a|
    ensures ComputeStateAt(a, m, day) == 
        if day == 0 then 0
        else (ComputeStateAt(a, m, day - 1) + a[day - 1]) % m
{
    // This follows directly from the definition
}

lemma StateAtBounds(a: seq<int>, m: int, day: int)
    requires m >= 1
    requires day >= 0
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    ensures 0 <= ComputeStateAt(a, m, day) < m
{
    if day == 0 {
        assert ComputeStateAt(a, m, day) == 0;
    } else if day > |a| {
        StateAtBounds(a, m, |a|);
    } else {
        StateAtBounds(a, m, day - 1);
        assert ComputeStateAt(a, m, day) == (ComputeStateAt(a, m, day - 1) + a[day - 1]) % m;
        assert 0 <= ComputeStateAt(a, m, day) < m;
    }
}

lemma ComputeStateCorrect(a: seq<int>, m: int, i: int, s: int)
    requires m >= 1
    requires 0 <= i <= |a|
    requires s == ComputeStateAt(a, m, i)
    requires i < |a|
    ensures (s + a[i]) % m == ComputeStateAt(a, m, i + 1)
{
    ComputeStateAtInductive(a, m, i + 1);
}

lemma ResultCorrectAtIndex(a: seq<int>, m: int, i: int)
    requires m >= 1
    requires 0 <= i < |a|
    requires forall k :: 0 <= k < |a| ==> a[k] >= 1
    ensures (ComputeStateAt(a, m, i) + a[i]) / m >= 0
{
    StateAtBounds(a, m, i);
    assert 0 <= ComputeStateAt(a, m, i) < m;
    assert a[i] >= 1;
    assert ComputeStateAt(a, m, i) + a[i] >= 0 + 1;
    assert ComputeStateAt(a, m, i) + a[i] >= 1;
    assert (ComputeStateAt(a, m, i) + a[i]) / m >= 0;
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
        invariant i == |result|
        invariant 0 <= s < m
        invariant s == ComputeStateAt(a, m, i)
        invariant forall j :: 0 <= j < i ==> result[j] == (ComputeStateAt(a, m, j) + a[j]) / m
        invariant forall j :: 0 <= j < i ==> result[j] >= 0
    {
        ResultCorrectAtIndex(a, m, i);
        var pageTurns := (s + a[i]) / m;
        assert pageTurns >= 0;
        assert pageTurns == (ComputeStateAt(a, m, i) + a[i]) / m;
        
        result := result + [pageTurns];
        
        assert |result| == i + 1;
        assert result[i] == pageTurns;
        assert forall j :: 0 <= j < i ==> result[j] == (ComputeStateAt(a, m, j) + a[j]) / m;
        
        ComputeStateCorrect(a, m, i, s);
        s := (s + a[i]) % m;
        i := i + 1;
        
        assert s == ComputeStateAt(a, m, i);
    }
    
    assert i == n;
    assert |result| == n;
}
// </vc-code>

