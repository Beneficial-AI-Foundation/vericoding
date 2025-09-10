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
lemma SumProperty(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures sum(s[..i]) + s[i] + sum(s[i+1..]) == sum(s)
{
    if i == 0 {
        assert s[..0] == [];
        assert sum([]) == 0;
        assert s[0..] == s;
    } else {
        assert s == s[..i] + [s[i]] + s[i+1..];
        if i == |s| - 1 {
            assert s[i+1..] == [];
            assert sum([]) == 0;
        }
    }
}

lemma SumAppend(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert sum([x]) == x + sum([]);
        assert sum([]) == 0;
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
    }
}

lemma SumInit(k: int)
    requires k > 0
    ensures sum(seq(k, i => i + 1)) == k * (k + 1) / 2
{
    if k == 1 {
        assert seq(1, i => i + 1) == [1];
    } else {
        var s := seq(k, i => i + 1);
        var s_prev := seq(k-1, i => i + 1);
        assert s == s_prev + [k];
        SumAppend(s_prev, k);
        SumInit(k-1);
    }
}

lemma SumReplace(s: seq<int>, i: int, newVal: int)
    requires 0 <= i < |s|
    ensures sum(s[..i] + [newVal] + s[i+1..]) == sum(s) - s[i] + newVal
{
    var s' := s[..i] + [newVal] + s[i+1..];
    SumProperty(s, i);
    assert sum(s) == sum(s[..i]) + s[i] + sum(s[i+1..]);
    
    if i < |s| - 1 {
        assert s'[..i] == s[..i];
        assert s'[i] == newVal;
        assert s'[i+1..] == s[i+1..];
        SumProperty(s', i);
        assert sum(s') == sum(s'[..i]) + s'[i] + sum(s'[i+1..]);
        assert sum(s') == sum(s[..i]) + newVal + sum(s[i+1..]);
    } else {
        assert i == |s| - 1;
        assert s[i+1..] == [];
        assert s' == s[..i] + [newVal];
        SumAppend(s[..i], newVal);
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
    var minSum := k * (k + 1) / 2;
    
    if n < minSum {
        return [-1];
    }
    
    // Create initial sequence 1, 2, ..., k
    var s := seq(k, i => i + 1);
    
    // We need to add (n - minSum) to the sequence
    var remainder := n - minSum;
    
    // Add the remainder to the last element
    var oldLast := s[k-1];
    s := s[..k-1] + [oldLast + remainder];
    
    // Verify sum property using SumInit and SumReplace
    SumInit(k);
    var init_seq := seq(k, i => i + 1);
    assert sum(init_seq) == minSum;
    
    // s is init_seq with last element replaced
    assert s == init_seq[..k-1] + [init_seq[k-1] + remainder];
    SumReplace(init_seq, k-1, init_seq[k-1] + remainder);
    assert sum(s) == sum(init_seq) - init_seq[k-1] + (init_seq[k-1] + remainder);
    assert sum(s) == sum(init_seq) + remainder;
    assert sum(s) == minSum + remainder;
    assert sum(s) == n;
    
    // Verify other properties
    assert |s| == k;
    
    // All positive: initial sequence has all positive, and we only increased the last element
    assert forall i :: 0 <= i < k-1 ==> s[i] == i + 1 > 0;
    assert s[k-1] == k + remainder >= k > 0;
    assert AllPositive(s);
    
    // Strictly increasing: first k-1 elements are 1,2,...,k-1
    // Last element is k + remainder >= k > k-1
    assert forall i :: 0 <= i < k-2 ==> s[i] == i + 1 < i + 2 == s[i+1];
    if k > 1 {
        assert s[k-2] == k - 1;
        assert s[k-1] == k + remainder;
        assert s[k-2] < s[k-1];
    }
    assert IsStrictlyIncreasing(s);
    
    assert ValidSequence(s, n, k);
    
    return s;
}
// </vc-code>

