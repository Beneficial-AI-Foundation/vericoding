predicate ValidInput(n: int, k: int)
{
    n > 0 && k > 0
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] > 0
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidSequence(s: seq<int>, n: int, k: int)
{
    |s| == k && AllPositive(s) && IsStrictlyIncreasing(s) && sum(s) == n
}

predicate IsPossible(n: int, k: int)
{
    k * (k + 1) / 2 <= n
}

// <vc-helpers>
lemma SumDistributive(s: seq<int>, i: int, val: int)
    requires 0 <= i < |s|
    ensures sum(s[i := s[i] + val]) == sum(s) + val
{
    if i == 0 {
        assert s[i := s[i] + val] == [s[0] + val] + s[1..];
        assert sum(s[i := s[i] + val]) == s[0] + val + sum(s[1..]) == sum(s) + val;
    } else {
        var s' := s[i := s[i] + val];
        assert s'[1..] == s[1..][i-1 := s[i] + val];
        SumDistributive(s[1..], i-1, val);
        assert sum(s'[1..]) == sum(s[1..]) + val;
        assert sum(s') == s'[0] + sum(s'[1..]) == s[0] + sum(s[1..]) + val == sum(s) + val;
    }
}

lemma SeqExtensionSum(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert sum(s + [x]) == sum(s) + x;
    } else {
        var extended := s + [x];
        assert extended[1..] == s[1..] + [x];
        SeqExtensionSum(s[1..], x);
        assert sum(extended[1..]) == sum(s[1..]) + x;
        assert sum(extended) == extended[0] + sum(extended[1..]) == s[0] + sum(s[1..]) + x == sum(s) + x;
    }
}

lemma BaseSequenceSum(k: int)
    requires k > 0
    ensures sum(seq(k, i => i + 1)) == k * (k + 1) / 2
{
    var s := seq(k, i => i + 1);
    if k == 1 {
        assert s == [1];
        assert sum(s) == 1 == 1 * 2 / 2;
    } else {
        var s_prev := seq(k-1, i => i + 1);
        
        // Establish that s == s_prev + [k]
        assert |s_prev + [k]| == k == |s|;
        forall i | 0 <= i < k
            ensures (s_prev + [k])[i] == s[i]
        {
            if i < k-1 {
                assert (s_prev + [k])[i] == s_prev[i] == i + 1 == s[i];
            } else {
                assert i == k-1;
                assert (s_prev + [k])[i] == k == s[i];
            }
        }
        assert s == s_prev + [k];
        
        SeqExtensionSum(s_prev, k);
        BaseSequenceSum(k-1);
        assert sum(s) == sum(s_prev) + k == (k-1) * k / 2 + k == k * (k + 1) / 2;
    }
}

lemma BaseSequenceProperties(k: int)
    requires k > 0
    ensures var s := seq(k, i => i + 1); |s| == k && AllPositive(s) && IsStrictlyIncreasing(s)
{
    var s := seq(k, i => i + 1);
    
    forall i | 0 <= i < |s|
        ensures s[i] > 0
    {
        assert s[i] == i + 1 > 0;
    }
    
    forall i | 0 <= i < |s| - 1
        ensures s[i] < s[i+1]
    {
        assert s[i] == i + 1;
        assert s[i+1] == (i + 1) + 1 == i + 2;
        assert s[i] < s[i+1];
    }
}

lemma UpdateLastPreservesProperties(s: seq<int>, val: int)
    requires |s| > 0 && AllPositive(s) && IsStrictlyIncreasing(s) && val >= 0
    ensures var s' := s[|s|-1 := s[|s|-1] + val]; AllPositive(s') && IsStrictlyIncreasing(s')
{
    var s' := s[|s|-1 := s[|s|-1] + val];
    var last := |s| - 1;
    
    forall i | 0 <= i < |s'|
        ensures s'[i] > 0
    {
        if i == last {
            assert s'[i] == s[i] + val >= s[i] > 0;
        } else {
            assert s'[i] == s[i] > 0;
        }
    }
    
    forall i | 0 <= i < |s'| - 1
        ensures s'[i] < s'[i+1]
    {
        if i == last - 1 {
            assert s'[i] == s[i];
            assert s'[i+1] == s[i+1] + val;
            assert s[i] < s[i+1];
            assert s'[i] < s'[i+1];
        } else {
            assert s'[i] == s[i] && s'[i+1] == s[i+1];
            assert s[i] < s[i+1];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures (|result| == 1 && result[0] == -1) || 
            (ValidSequence(result, n, k))
    ensures (|result| == 1 && result[0] == -1) <==> !IsPossible(n, k)
// </vc-spec>
// <vc-code>
{
    if k * (k + 1) / 2 > n {
        return [-1];
    }
    
    var base := seq(k, i => i + 1);
    BaseSequenceSum(k);
    BaseSequenceProperties(k);
    
    var remaining := n - k * (k + 1) / 2;
    var finalResult := base[k-1 := base[k-1] + remaining];
    
    SumDistributive(base, k-1, remaining);
    UpdateLastPreservesProperties(base, remaining);
    
    return finalResult;
}
// </vc-code>

