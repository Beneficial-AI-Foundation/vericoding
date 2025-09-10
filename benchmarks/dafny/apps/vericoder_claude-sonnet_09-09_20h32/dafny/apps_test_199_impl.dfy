predicate ValidInput(n: int, s: int, v: seq<int>)
{
    n > 0 && |v| == n && s >= 0 && forall i :: 0 <= i < |v| ==> v[i] >= 0
}

function sum(v: seq<int>): int
{
    if |v| == 0 then 0
    else v[0] + sum(v[1..])
}

function minSeq(v: seq<int>): int
    requires |v| > 0
    ensures (forall i :: 0 <= i < |v| ==> v[i] >= 0) ==> minSeq(v) >= 0
{
    if |v| == 1 then v[0]
    else if v[0] <= minSeq(v[1..]) then v[0]
    else minSeq(v[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

// <vc-helpers>
lemma SumNonNegative(v: seq<int>)
    requires forall i :: 0 <= i < |v| ==> v[i] >= 0
    ensures sum(v) >= 0
{
    if |v| == 0 {
    } else {
        SumNonNegative(v[1..]);
    }
}

lemma DivisionNonNegative(a: int, b: int)
    requires a >= 0 && b > 0
    ensures a / b >= 0
{
}

lemma MinNonNegative(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures min(a, b) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: int, v: seq<int>) returns (result: int)
    requires ValidInput(n, s, v)
    ensures sum(v) < s ==> result == -1
    ensures sum(v) >= s ==> result == min((sum(v) - s) / n, minSeq(v))
    ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
    var totalSum := sum(v);
    if totalSum < s {
        result := -1;
    } else {
        var diff := totalSum - s;
        var quotient := diff / n;
        var minVal := minSeq(v);
        
        SumNonNegative(v);
        DivisionNonNegative(diff, n);
        MinNonNegative(quotient, minVal);
        
        result := min(quotient, minVal);
    }
}
// </vc-code>

