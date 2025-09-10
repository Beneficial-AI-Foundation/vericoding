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
lemma ComputeFinalLIterative(pairs: seq<(int, int)>, i: int)
    requires 0 <= i <= |pairs|
    ensures computeFinalL(pairs[..i]) == 
        if i == 0 then 1
        else var L := computeFinalL(pairs[..i-1]);
             var minVal := if pairs[i-1].0 < pairs[i-1].1 then pairs[i-1].0 else pairs[i-1].1;
             if L > minVal then L else minVal
{
    if i == 0 {
        assert pairs[..0] == [];
    } else {
        assert pairs[..i] == pairs[..i-1] + [pairs[i-1]];
        assert pairs[..i][..i-1] == pairs[..i-1];
    }
}

lemma ComputeFinalRIterative(n: int, pairs: seq<(int, int)>, i: int)
    requires 0 <= i <= |pairs|
    ensures computeFinalR(n, pairs[..i]) == 
        if i == 0 then n
        else var R := computeFinalR(n, pairs[..i-1]);
             var maxVal := if pairs[i-1].0 > pairs[i-1].1 then pairs[i-1].0 else pairs[i-1].1;
             if R < maxVal then R else maxVal
{
    if i == 0 {
        assert pairs[..0] == [];
    } else {
        assert pairs[..i] == pairs[..i-1] + [pairs[i-1]];
        assert pairs[..i][..i-1] == pairs[..i-1];
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, pairs: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, m, pairs)
    ensures ValidResult(n, pairs, result)
// </vc-spec>
// <vc-code>
{
    var L := 1;
    var R := n;
    var i := 0;
    
    while i < |pairs|
        invariant 0 <= i <= |pairs|
        invariant L == computeFinalL(pairs[..i])
        invariant R == computeFinalR(n, pairs[..i])
    {
        var x := pairs[i].0;
        var y := pairs[i].1;
        var minVal := if x < y then x else y;
        var maxVal := if x > y then x else y;
        
        ComputeFinalLIterative(pairs, i + 1);
        ComputeFinalRIterative(n, pairs, i + 1);
        
        L := if L > minVal then L else minVal;
        R := if R < maxVal then R else maxVal;
        
        i := i + 1;
    }
    
    assert pairs[..|pairs|] == pairs;
    assert L == computeFinalL(pairs);
    assert R == computeFinalR(n, pairs);
    
    result := if R > L then R - L else 0;
    assert result == max(R - L, 0);
}
// </vc-code>

