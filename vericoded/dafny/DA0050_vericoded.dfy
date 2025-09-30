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
        // Base case: sum of empty sequence is 0
    } else {
        // Recursive case: v[0] >= 0 and sum(v[1..]) >= 0
        SumNonNegative(v[1..]);
    }
}

lemma MinSeqIsInSequence(v: seq<int>)
    requires |v| > 0
    ensures exists i :: 0 <= i < |v| && v[i] == minSeq(v)
{
    if |v| == 1 {
        // Base case: the only element is the minimum
        assert v[0] == minSeq(v);
    } else {
        // Recursive case
        MinSeqIsInSequence(v[1..]);
        if v[0] <= minSeq(v[1..]) {
            assert v[0] == minSeq(v);
        } else {
            var i :| 0 <= i < |v[1..]| && v[1..][i] == minSeq(v[1..]);
            assert v[i+1] == minSeq(v);
        }
    }
}

lemma MinSeqLowerBound(v: seq<int>)
    requires |v| > 0
    ensures forall i :: 0 <= i < |v| ==> minSeq(v) <= v[i]
{
    if |v| == 1 {
        // Base case
    } else {
        // Recursive case
        MinSeqLowerBound(v[1..]);
        forall i | 0 <= i < |v|
            ensures minSeq(v) <= v[i]
        {
            if i == 0 {
                // minSeq(v) is either v[0] or something from v[1..], both <= v[0]
            } else {
                assert v[i] == v[1..][i-1];
                assert minSeq(v[1..]) <= v[1..][i-1];
            }
        }
    }
}

lemma SumAppend(v: seq<int>, x: int)
    ensures sum(v + [x]) == sum(v) + x
{
    if |v| == 0 {
        assert v + [x] == [x];
        assert sum([x]) == x;
    } else {
        assert (v + [x])[0] == v[0];
        assert (v + [x])[1..] == v[1..] + [x];
        SumAppend(v[1..], x);
    }
}

lemma MinSeqAppend(v: seq<int>, x: int)
    requires |v| > 0
    ensures minSeq(v + [x]) == if x < minSeq(v) then x else minSeq(v)
{
    if |v| == 1 {
        assert v + [x] == [v[0], x];
        assert minSeq([v[0], x]) == if v[0] <= x then v[0] else x;
        assert minSeq(v) == v[0];
    } else {
        assert (v + [x])[0] == v[0];
        assert (v + [x])[1..] == v[1..] + [x];
        MinSeqAppend(v[1..], x);
        if v[0] <= minSeq(v[1..]) {
            assert minSeq(v) == v[0];
            if x < v[0] {
                assert minSeq(v + [x]) == x;
            } else {
                assert minSeq(v + [x]) == v[0];
            }
        } else {
            assert minSeq(v) == minSeq(v[1..]);
            if x < minSeq(v[1..]) {
                assert minSeq(v + [x]) == x;
            } else {
                assert minSeq(v + [x]) == minSeq(v[1..]);
            }
        }
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
    var totalSum := 0;
    var i := 0;
    
    // Calculate sum
    while i < n
        invariant 0 <= i <= n
        invariant n == |v|
        invariant totalSum == sum(v[..i])
    {
        assert v[..i+1] == v[..i] + [v[i]];
        SumAppend(v[..i], v[i]);
        assert sum(v[..i+1]) == sum(v[..i]) + v[i];
        totalSum := totalSum + v[i];
        i := i + 1;
    }
    
    assert v[..n] == v;
    assert totalSum == sum(v);
    
    if totalSum < s {
        result := -1;
    } else {
        // Find minimum element
        var minVal := v[0];
        i := 1;
        
        while i < n
            invariant 1 <= i <= n
            invariant n == |v|
            invariant minVal == minSeq(v[..i])
            invariant forall j :: 0 <= j < i ==> minVal <= v[j]
        {
            assert v[..i+1] == v[..i] + [v[i]];
            MinSeqAppend(v[..i], v[i]);
            assert minSeq(v[..i+1]) == if v[i] < minSeq(v[..i]) then v[i] else minSeq(v[..i]);
            
            if v[i] < minVal {
                minVal := v[i];
            }
            i := i + 1;
        }
        
        assert v[..n] == v;
        assert minVal == minSeq(v);
        
        var diff := totalSum - s;
        var quotient := diff / n;
        
        if quotient <= minVal {
            result := quotient;
        } else {
            result := minVal;
        }
        
        assert result == min((sum(v) - s) / n, minSeq(v));
        
        // Prove result >= 0
        SumNonNegative(v);
        assert sum(v) >= 0;
        assert sum(v) >= s;
        assert diff >= 0;
        assert quotient >= 0;
        assert minSeq(v) >= 0;
        assert result >= 0;
    }
}
// </vc-code>

