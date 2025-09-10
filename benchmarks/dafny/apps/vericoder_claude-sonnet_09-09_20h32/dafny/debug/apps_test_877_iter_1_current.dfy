predicate ValidInput(n: int, m: int, pairs: seq<(int, int)>)
{
    n >= 2 && 
    m >= 0 && 
    |pairs| == m &&
    (forall i :: 0 <= i < |pairs| ==> 1 <= pairs[i].0 <= n && 1 <= pairs[i].1 <= n) &&
    (forall i :: 0 <= i < |pairs| ==> pairs[i].0 != pairs[i].1)
}

function computeFinalL(pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then 1
    else 
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var minVal := if x < y then x else y;
        var restL := computeFinalL(pairs[..|pairs|-1]);
        if restL > minVal then restL else minVal
}

function computeFinalR(n: int, pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then n
    else
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var maxVal := if x > y then x else y;
        var restR := computeFinalR(n, pairs[..|pairs|-1]);
        if restR < maxVal then restR else maxVal
}

function max(a: int, b: int): int
{
    if a > b then a else b
}

predicate ValidResult(n: int, pairs: seq<(int, int)>, result: int)
{
    result >= 0 &&
    result <= n - 1 &&
    result == max(computeFinalR(n, pairs) - computeFinalL(pairs), 0)
}

// <vc-helpers>
lemma computeFinalLMonotonic(pairs: seq<(int, int)>, i: int)
    requires 0 <= i < |pairs|
    ensures computeFinalL(pairs[..i+1]) >= computeFinalL(pairs[..i])
{
    if i == 0 {
        assert pairs[..1] == [pairs[0]];
        assert pairs[..0] == [];
    } else {
        var prefix := pairs[..i+1];
        var shorterPrefix := pairs[..i];
        assert prefix == shorterPrefix + [pairs[i]];
    }
}

lemma computeFinalRMonotonic(n: int, pairs: seq<(int, int)>, i: int)
    requires 0 <= i < |pairs|
    ensures computeFinalR(n, pairs[..i+1]) <= computeFinalR(n, pairs[..i])
{
    if i == 0 {
        assert pairs[..1] == [pairs[0]];
        assert pairs[..0] == [];
    } else {
        var prefix := pairs[..i+1];
        var shorterPrefix := pairs[..i];
        assert prefix == shorterPrefix + [pairs[i]];
    }
}

lemma computeFinalLIterative(pairs: seq<(int, int)>, i: int, currentL: int)
    requires 0 <= i <= |pairs|
    requires currentL == computeFinalL(pairs[..i])
    requires i < |pairs|
    ensures if currentL > (if pairs[i].0 < pairs[i].1 then pairs[i].0 else pairs[i].1) 
            then currentL 
            else (if pairs[i].0 < pairs[i].1 then pairs[i].0 else pairs[i].1) 
            == computeFinalL(pairs[..i+1])
{
    var newPrefix := pairs[..i+1];
    assert newPrefix == pairs[..i] + [pairs[i]];
}

lemma computeFinalRIterative(n: int, pairs: seq<(int, int)>, i: int, currentR: int)
    requires 0 <= i <= |pairs|
    requires currentR == computeFinalR(n, pairs[..i])
    requires i < |pairs|
    ensures if currentR < (if pairs[i].0 > pairs[i].1 then pairs[i].0 else pairs[i].1) 
            then currentR 
            else (if pairs[i].0 > pairs[i].1 then pairs[i].0 else pairs[i].1) 
            == computeFinalR(n, pairs[..i+1])
{
    var newPrefix := pairs[..i+1];
    assert newPrefix == pairs[..i] + [pairs[i]];
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, pairs: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, m, pairs)
    ensures ValidResult(n, pairs, result)
// </vc-spec>
// <vc-code>
{
    var l := 1;
    var r := n;
    var i := 0;
    
    while i < m
        invariant 0 <= i <= m
        invariant l == computeFinalL(pairs[..i])
        invariant r == computeFinalR(n, pairs[..i])
    {
        var x := pairs[i].0;
        var y := pairs[i].1;
        var minVal := if x < y then x else y;
        var maxVal := if x > y then x else y;
        
        computeFinalLIterative(pairs, i, l);
        computeFinalRIterative(n, pairs, i, r);
        
        l := if l > minVal then l else minVal;
        r := if r < maxVal then r else maxVal;
        i := i + 1;
    }
    
    assert pairs[..i] == pairs[..m] == pairs;
    
    var diff := r - l;
    result := if diff > 0 then diff else 0;
    assert result == max(r - l, 0);
}
// </vc-code>

