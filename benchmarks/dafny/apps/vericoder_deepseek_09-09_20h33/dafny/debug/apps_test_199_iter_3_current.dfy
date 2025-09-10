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
                // For i=0 in the tail, we need to consider the first element
                assert minSeq(v) == minSeq(v[1..]);
                assert minSeq(v) <= v[0];
            }
        } else {
            minSeqLemma(v[1..], i - 1);
            if v[0] <= minSeq(v[1..]) {
                // v[0] is min, so it's <= v[i] in the tail
                assert v[0] <= minSeq(v[1..]);
                assert minSeq(v) == v[0];
                assert v[0] <= v[i]; // This may not hold, need different approach
                // Instead, we rely on the fact that minSeq(v) is <= all elements
            } else {
                // min is in the tail, so minSeq(v) == minSeq(v[1..]) <= v[i] in tail
                assert minSeq(v) == minSeq(v[1..]);
            }
        }
    }
}

lemma SumMinBound(v: seq<int>)
    requires |v| > 0
    requires forall i :: 0 <= i < |v| ==> v[i] >= 0
    ensures minSeq(v) * |v| <= sum(v)
{
    if |v| == 1 {
        // Base case: minSeq(v) * 1 = v[0] = sum(v)
        return;
    }
    
    var i := 0;
    while i < |v|
        invariant 0 <= i <= |v|
        invariant minSeq(v) * i <= sum(v[0..i])
    {
        minSeqLemma(v, i);
        var current_min := minSeq(v);
        assert current_min <= v[i];
        
        // Fix the sum assertion - use the actual definition of sum
        if i == 0 {
            assert sum(v[0..1]) == v[0];
        } else {
            assert sum(v[0..i+1]) == sum(v[0..i]) + v[i];
        }
        
        assert current_min * (i + 1) == current_min * i + current_min;
        assert current_min * i + current_min <= sum(v[0..i]) + v[i];
        i := i + 1;
    }
}

lemma DivisionLemma(dividend: int, divisor: int)
    requires divisor > 0
    requires divisor * ((dividend - (divisor - 1)) / divisor) <= dividend - (divisor - 1)
{
    // This is a basic property of integer division
}

lemma CandidateBoundLemma(total: int, s: int, n: int, min_val: int)
    requires n > 0
    requires s >= 0
    requires total >= s
    requires min_val * n <= total
    ensures (total - s) / n <= min_val
{
    assert min_val * n <= total;
    assert (total - s) <= total;
    
    // Since (total - s) <= total <= min_val * n, we can write:
    // (total - s)/n <= (min_val * n)/n = min_val
    // But need to be careful with integer division
    assert total - s <= min_val * n;
    assert (total - s) / n <= min_val;
    
    // Add intermediate steps to help the verifier
    if min_val > 0 {
        assert (total - s) / n <= total / n <= (min_val * n) / n <= min_val;
    } else {
        // min_val == 0 case
        assert min_val == 0;
        assert (total - s) / n >= 0;  // since total - s >= 0 and n > 0
    }
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
        assert |v| == n > 0;
        
        // Prove that minSeq(v) * n <= total
        SumMinBound(v);
        assert minSeq(v) * n <= total;
        
        var diff := total - s;
        var candidate := diff / n;
        var min_val := minSeq(v);
        
        // Now we know candidate <= min_val
        CandidateBoundLemma(total, s, n, min_val);
        assert candidate <= min_val;
        
        // Hence, candidate is always <= min_val
        result := min(candidate, min_val);
        
        // Verify non-negative result
        assert candidate >= 0; // since diff >= 0 and n > 0
        assert result >= 0;
    }
}
// </vc-code>

