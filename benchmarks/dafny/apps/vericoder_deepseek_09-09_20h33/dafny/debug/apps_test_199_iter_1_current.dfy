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
lemma minSeqLemma(v: seq<int>, i: int)
    requires |v| > 0
    requires forall i :: 0 <= i < |v| ==> v[i] >= 0
    requires 0 <= i < |v|
    ensures minSeq(v) <= v[i]
{
    if |v| == 1 {
        // trivial case
    } else {
        if i == 0 {
            // v[0] is either the min or we look at the rest
            if v[0] <= minSeq(v[1..]) {
                // v[0] is the minimum
            } else {
                minSeqLemma(v[1..], i - 1);
            }
        } else {
            minSeqLemma(v[1..], i - 1);
            if v[0] <= minSeq(v[1..]) {
                // v[0] is min, so it's <= v[i] in the tail
            } else {
                // min is in the tail, so minSeq(v) == minSeq(v[1..]) <= v[i] in tail
            }
        }
    }
}

lemma SumMinBound(v: seq<int>)
    requires |v| > 0
    requires forall i :: 0 <= i < |v| ==> v[i] >= 0
    ensures minSeq(v) * |v| <= sum(v)
{
    var i := 0;
    while i < |v|
        invariant 0 <= i <= |v|
        invariant minSeq(v) * i <= sum(v[0..i])
    {
        minSeqLemma(v, i);
        i := i + 1;
    }
}

lemma DivisionLemma(dividend: int, divisor: int)
    requires divisor > 0
    requires divisor * ((dividend - (divisor - 1)) / divisor) <= dividend - (divisor - 1)
{
    // This is a basic property of integer division
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
    var total := sum(v);
    if total < s {
        result := -1;
    } else {
        var diff := total - s;
        var candidate := diff / n;
        var min_val := minSeq(v);
        
        // We know: min_val * n <= total (since each element >= min_val)
        // So: candidate = (total - s)/n <= (total)/n <= (min_val * n)/n = min_val
        
        if candidate <= min_val {
            result := candidate;
        } else {
            result := min_val;
        }
        
        // Verify non-negative result
        assert result >= 0;
    }
}
// </vc-code>

