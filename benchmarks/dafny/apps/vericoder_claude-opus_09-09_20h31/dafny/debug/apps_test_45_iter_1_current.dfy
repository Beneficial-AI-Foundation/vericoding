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
    s := s[..k-1] + [s[k-1] + remainder];
    
    // Verify sum property
    SumInit(k);
    assert sum(seq(k, i => i + 1)) == minSum;
    
    var init_seq := seq(k, i => i + 1);
    assert s[..k-1] == init_seq[..k-1];
    assert s[k-1] == init_seq[k-1] + remainder;
    
    // Helper assertions for sum
    assert sum(s[..k-1]) == sum(init_seq[..k-1]);
    SumProperty(init_seq, k-1);
    assert sum(init_seq[..k-1]) + init_seq[k-1] == sum(init_seq);
    assert sum(s[..k-1]) + s[k-1] == sum(init_seq[..k-1]) + init_seq[k-1] + remainder;
    assert sum(s[..k-1]) + s[k-1] == sum(init_seq) + remainder;
    assert sum(s[..k-1]) + s[k-1] == minSum + remainder;
    assert sum(s[..k-1]) + s[k-1] == n;
    
    // Verify sum of modified sequence
    assert s == s[..k-1] + [s[k-1]];
    assert sum(s) == sum(s[..k-1] + [s[k-1]]);
    SumAppend(s[..k-1], s[k-1]);
    assert sum(s) == n;
    
    return s;
}
// </vc-code>

