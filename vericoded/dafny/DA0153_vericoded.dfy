predicate ValidInput(n: int, a: seq<int>) {
    n >= 1 && n <= 90 &&
    |a| == n &&
    (forall i :: 0 <= i < n ==> 1 <= a[i] <= 90) &&
    (forall i :: 0 <= i < n - 1 ==> a[i] < a[i + 1])
}

function findCutoff(a: seq<int>, index: int, cutoff: int): int
    requires 0 <= index <= |a|
    decreases |a| - index
{
    if index >= |a| then cutoff
    else if a[index] > cutoff then cutoff
    else findCutoff(a, index + 1, a[index] + 15)
}

function min(x: int, y: int): int
{
    if x <= y then x else y
}

predicate ValidOutput(result: int, n: int, a: seq<int>) {
    ValidInput(n, a) ==>
    (1 <= result <= 90 &&
     result == min(90, findCutoff(a, 0, 15)))
}

// <vc-helpers>
lemma findCutoffIterative(a: seq<int>, index: int, cutoff: int)
    requires 0 <= index <= |a|
    ensures findCutoff(a, index, cutoff) == 
        if index >= |a| then cutoff
        else if a[index] > cutoff then cutoff
        else findCutoff(a, index + 1, a[index] + 15)
    decreases |a| - index
{
    // This follows directly from the definition of findCutoff
}

lemma findCutoffStep(a: seq<int>, i: int, c: int)
    requires 0 <= i < |a|
    requires a[i] <= c
    ensures findCutoff(a, i, c) == findCutoff(a, i + 1, a[i] + 15)
{
    // By definition of findCutoff
}

lemma findCutoffTerminate(a: seq<int>, i: int, c: int)
    requires 0 <= i < |a|
    requires a[i] > c
    ensures findCutoff(a, i, c) == c
{
    // By definition of findCutoff
}

lemma findCutoffEnd(a: seq<int>, c: int)
    requires 0 <= |a|
    ensures findCutoff(a, |a|, c) == c
{
    // By definition of findCutoff
}

lemma findCutoffLowerBound(a: seq<int>, index: int, cutoff: int)
    requires 0 <= index <= |a|
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1
    requires cutoff >= 15
    ensures findCutoff(a, index, cutoff) >= 15
    decreases |a| - index
{
    if index >= |a| {
        assert findCutoff(a, index, cutoff) == cutoff >= 15;
    } else if a[index] > cutoff {
        assert findCutoff(a, index, cutoff) == cutoff >= 15;
    } else {
        assert a[index] >= 1;
        assert a[index] + 15 >= 16 >= 15;
        findCutoffLowerBound(a, index + 1, a[index] + 15);
        assert findCutoff(a, index + 1, a[index] + 15) >= 15;
        assert findCutoff(a, index, cutoff) == findCutoff(a, index + 1, a[index] + 15) >= 15;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures ValidOutput(result, n, a)
// </vc-spec>
// <vc-code>
{
    var i := 0;
    var cutoff := 15;
    
    while i < |a| && a[i] <= cutoff
        invariant 0 <= i <= |a|
        invariant cutoff >= 15
        invariant forall j :: 0 <= j < i ==> a[j] >= 1
        invariant findCutoff(a, i, cutoff) == findCutoff(a, 0, 15)
        decreases |a| - i
    {
        var oldCutoff := cutoff;
        var oldI := i;
        assert a[i] >= 1;  // from ValidInput
        cutoff := a[i] + 15;
        assert cutoff >= 16 >= 15;
        i := i + 1;
        
        assert a[oldI] <= oldCutoff;
        findCutoffStep(a, oldI, oldCutoff);
        assert findCutoff(a, oldI, oldCutoff) == findCutoff(a, i, cutoff);
    }
    
    if i < |a| {
        assert a[i] > cutoff;
        findCutoffTerminate(a, i, cutoff);
        assert findCutoff(a, i, cutoff) == cutoff;
    } else {
        assert i == |a|;
        findCutoffEnd(a, cutoff);
        assert findCutoff(a, i, cutoff) == cutoff;
    }
    
    assert findCutoff(a, i, cutoff) == cutoff;
    assert findCutoff(a, 0, 15) == cutoff;
    assert cutoff >= 15;
    
    // Apply the lemma to prove findCutoff(a, 0, 15) >= 15
    assert forall j :: 0 <= j < |a| ==> a[j] >= 1;  // from ValidInput
    findCutoffLowerBound(a, 0, 15);
    assert findCutoff(a, 0, 15) >= 15;
    
    result := min(90, cutoff);
    
    assert result == min(90, findCutoff(a, 0, 15));
    assert findCutoff(a, 0, 15) >= 15;
    assert result >= min(90, 15);
    assert result >= 15;
    assert result >= 1;
    assert result <= 90;
    assert 1 <= result <= 90;
    assert ValidOutput(result, n, a);
}
// </vc-code>

