function sum(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidInput(n: int, k: int, a: seq<int>)
{
    n >= 1 && |a| == n && k >= 0 && forall i :: 0 <= i < n ==> a[i] >= 0
}

predicate ValidOutput(a: seq<int>, finalSchedule: seq<int>, additionalWalks: int, k: int)
{
    |finalSchedule| == |a| &&
    additionalWalks >= 0 &&
    forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i] &&
    forall i :: 0 <= i < |a| - 1 ==> finalSchedule[i] + finalSchedule[i + 1] >= k &&
    additionalWalks == sum(finalSchedule) - sum(a)
}

// <vc-helpers>
lemma SumDistributive(s1: seq<int>, s2: seq<int>)
    requires |s1| == |s2|
    ensures sum(s1) + sum(s2) == sum(seq(|s1|, i requires 0 <= i < |s1| => s1[i] + s2[i]))
{
    if |s1| == 0 {
        assert sum(s1) == 0;
        assert sum(s2) == 0;
        var emptySum := seq(0, i requires 0 <= i < 0 => s1[i] + s2[i]);
        assert emptySum == [];
        assert sum(emptySum) == 0;
    } else {
        var combined := seq(|s1|, i requires 0 <= i < |s1| => s1[i] + s2[i]);
        assert combined[0] == s1[0] + s2[0];
        var s1Tail := s1[1..];
        var s2Tail := s2[1..];
        var combinedTail := seq(|s1Tail|, i requires 0 <= i < |s1Tail| => s1Tail[i] + s2Tail[i]);
        assert combinedTail == combined[1..];
        SumDistributive(s1Tail, s2Tail);
        assert sum(s1Tail) + sum(s2Tail) == sum(combinedTail);
        assert sum(combined) == combined[0] + sum(combined[1..]);
        assert sum(combined) == (s1[0] + s2[0]) + sum(combinedTail);
        assert sum(combined) == s1[0] + s2[0] + sum(s1Tail) + sum(s2Tail);
        assert sum(s1) == s1[0] + sum(s1Tail);
        assert sum(s2) == s2[0] + sum(s2Tail);
    }
}

lemma SumNonNegative(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures sum(s) >= 0
{
    if |s| == 0 {
    } else {
        SumNonNegative(s[1..]);
    }
}

lemma SumMonotonic(s1: seq<int>, s2: seq<int>)
    requires |s1| == |s2|
    requires forall i :: 0 <= i < |s1| ==> s1[i] <= s2[i]
    ensures sum(s1) <= sum(s2)
{
    if |s1| == 0 {
    } else {
        SumMonotonic(s1[1..], s2[1..]);
    }
}

lemma DifferenceSequenceProperty(a: seq<int>, finalSchedule: seq<int>)
    requires |a| == |finalSchedule|
    requires forall i :: 0 <= i < |a| ==> finalSchedule[i] >= a[i]
    ensures sum(finalSchedule) - sum(a) == sum(seq(|a|, i requires 0 <= i < |a| => finalSchedule[i] - a[i]))
{
    var diff := seq(|a|, i requires 0 <= i < |a| => finalSchedule[i] - a[i]);
    var sumSeq := seq(|a|, i requires 0 <= i < |a| => a[i] + diff[i]);
    
    assert forall i :: 0 <= i < |a| ==> sumSeq[i] == a[i] + diff[i] == finalSchedule[i];
    assert sumSeq == finalSchedule;
    
    SumDistributive(a, diff);
    assert sum(a) + sum(diff) == sum(sumSeq);
    assert sum(a) + sum(diff) == sum(finalSchedule);
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
{
    finalSchedule := a;
    
    var i := 0;
    while i < |finalSchedule| - 1
        invariant 0 <= i <= |finalSchedule| - 1
        invariant |finalSchedule| == |a|
        invariant forall j {:trigger finalSchedule[j]} :: 0 <= j < |a| ==> finalSchedule[j] >= a[j]
        invariant forall j {:trigger finalSchedule[j], finalSchedule[j + 1]} :: 0 <= j < i ==> finalSchedule[j] + finalSchedule[j + 1] >= k
    {
        if finalSchedule[i] + finalSchedule[i + 1] < k {
            var needed := k - finalSchedule[i];
            finalSchedule := finalSchedule[i + 1 := needed];
        }
        i := i + 1;
    }
    
    SumMonotonic(a, finalSchedule);
    DifferenceSequenceProperty(a, finalSchedule);
    var diff := sum(finalSchedule) - sum(a);
    SumNonNegative(a);
    SumNonNegative(finalSchedule);
    
    additionalWalks := diff;
}
// </vc-code>

