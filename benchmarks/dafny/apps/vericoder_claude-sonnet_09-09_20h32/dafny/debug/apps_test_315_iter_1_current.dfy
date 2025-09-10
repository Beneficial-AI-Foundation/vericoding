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
    } else {
        SumDistributive(s1[1..], s2[1..]);
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
        invariant forall j :: 0 <= j < |a| ==> finalSchedule[j] >= a[j]
        invariant forall j :: 0 <= j < i ==> finalSchedule[j] + finalSchedule[j + 1] >= k
    {
        if finalSchedule[i] + finalSchedule[i + 1] < k {
            var needed := k - finalSchedule[i];
            finalSchedule := finalSchedule[i + 1 := needed];
        }
        i := i + 1;
    }
    
    SumMonotonic(a, finalSchedule);
    var diff := sum(finalSchedule) - sum(a);
    SumNonNegative(a);
    SumNonNegative(finalSchedule);
    
    additionalWalks := diff;
}
// </vc-code>

