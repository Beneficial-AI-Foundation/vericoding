predicate ValidInput(n: int, m: seq<int>) {
    n > 0 && |m| == n && 
    forall i :: 0 <= i < n ==> 0 <= m[i] < i + 1
}

predicate ValidSolution(n: int, m: seq<int>, dm: seq<int>) {
    |dm| == n && |m| == n &&
    (forall i :: 0 <= i < n ==> dm[i] >= m[i] + 1) &&
    (forall i :: 0 <= i < n - 1 ==> dm[i] <= dm[i + 1])
}

function SumBelow(m: seq<int>, dm: seq<int>): int
    requires |m| == |dm|
{
    if |m| == 0 then 0
    else (dm[0] - 1 - m[0]) + SumBelow(m[1..], dm[1..])
}

// <vc-helpers>
lemma SumBelowNonNegative(m: seq<int>, dm: seq<int>)
    requires |m| == |dm|
    requires forall i :: 0 <= i < |m| ==> dm[i] >= m[i] + 1
    ensures SumBelow(m, dm) >= 0
{
    if |m| == 0 {
    } else {
        assert dm[0] >= m[0] + 1;
        assert dm[0] - 1 - m[0] >= 0;
        SumBelowNonNegative(m[1..], dm[1..]);
    }
}

function ConstructSolution(n: int, m: seq<int>): seq<int>
    requires ValidInput(n, m)
    ensures |ConstructSolution(n, m)| == n
    ensures ValidSolution(n, m, ConstructSolution(n, m))
{
    if n == 0 then []
    else if n == 1 then [m[0] + 1]
    else 
        var prev := ConstructSolution(n-1, m[0..n-1]);
        var last_val := if prev[n-2] >= m[n-1] + 1 then prev[n-2] else m[n-1] + 1;
        prev + [last_val]
}

lemma ConstructSolutionValid(n: int, m: seq<int>)
    requires ValidInput(n, m)
    ensures ValidSolution(n, m, ConstructSolution(n, m))
{
    if n <= 1 {
    } else {
        ConstructSolutionValid(n-1, m[0..n-1]);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: seq<int>) returns (result: int)
    requires ValidInput(n, m)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    
    var dm := ConstructSolution(n, m);
    ConstructSolutionValid(n, m);
    SumBelowNonNegative(m, dm);
    
    result := SumBelow(m, dm);
}
// </vc-code>

