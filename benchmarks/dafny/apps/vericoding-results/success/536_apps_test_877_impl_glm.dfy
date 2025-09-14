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
lemma computeFinalL_upper_bound(n: int, pairs: seq<(int, int)>)
    requires ValidInput(n, |pairs|, pairs)
    ensures computeFinalL(pairs) <= n
{
    if |pairs| == 0 {
    } else {
        calc {
            computeFinalL(pairs);
            ==  // def computeFinalL
            var x := pairs[|pairs|-1].0;
            var y := pairs[|pairs|-1].1;
            var minVal := if x < y then x else y;
            var restL := computeFinalL(pairs[..|pairs|-1]);
            if restL > minVal then restL else minVal;
            <=  // x, y <= n by ValidInput. minVal <= x || minVal <= y => minVal <= n. By IH restL <= n. So both branches <= n.
            n;
        }
    }
}

lemma computeFinalR_lower_bound(n: int, pairs: seq<(int, int)>)
    requires ValidInput(n, |pairs|, pairs)
    ensures computeFinalR(n, pairs) >= 1
{
    if |pairs| == 0 {
        calc {
            computeFinalR(n, pairs);
            == // def computeFinalR
            n;
            >=  // n >= 2 by ValidInput
            1;
        }
    } else {
        calc {
            computeFinalR(n, pairs);
            ==  // def computeFinalR
            var x := pairs[|pairs|-1].0;
            var y := pairs[|pairs|-1].1;
            var maxVal := if x > y then x else y;
            var restR := computeFinalR(n, pairs[..|pairs|-1]);
            if restR < maxVal then restR else maxVal;
            >=  // x, y >= 1 by ValidInput. maxVal >= x || maxVal >= y => maxVal >= 1. By IH restR >= 1. So both branches >= 1.
            1;
        }
    }
}

lemma computeFinalL_ge_1(n: int, pairs: seq<(int, int)>)
    requires |pairs| >= 0 && (forall i :: 0 <= i < |pairs| ==> 1 <= pairs[i].0 <= n && 1 <= pairs[i].1 <= n)
    ensures computeFinalL(pairs) >= 1
{
    if |pairs| == 0 {
    } else {
        calc {
            computeFinalL(pairs);
            ==  // def computeFinalL
            var x := pairs[|pairs|-1].0;
            var y := pairs[|pairs|-1].1;
            var minVal := if x < y then x else y;
            var restL := computeFinalL(pairs[..|pairs|-1]);
            if restL > minVal then restL else minVal;
            >=  // x >= 1, y >= 1 => minVal >= 1. By IH restL >= 1. So both branches >= 1.
            1;
        }
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
    var finalL := computeFinalL(pairs);
    var finalR := computeFinalR(n, pairs);

    computeFinalL_upper_bound(n, pairs);
    computeFinalR_lower_bound(n, pairs);
    computeFinalL_ge_1(n, pairs);
    
    result := max(finalR - finalL, 0);
}
// </vc-code>

