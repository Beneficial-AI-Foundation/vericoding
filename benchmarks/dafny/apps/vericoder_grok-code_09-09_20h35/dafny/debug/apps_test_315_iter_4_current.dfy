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
// No updates needed after removing duplicates from preamble
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, a: seq<int>) returns (additionalWalks: int, finalSchedule: seq<int>)
    requires ValidInput(n, k, a)
    ensures ValidOutput(a, finalSchedule, additionalWalks, k)
// </vc-spec>
// <vc-code>
{
    var final := [];
    for i := 0 to n-1
        invariant |final| == i
        invariant forall j :: 0 <= j < i ==> final[j] >= a[j]
        invariant forall j :: 0 <= j < i - 1 ==> final[j] + final[j + 1] >= k
    {
        var prev := if i == 0 then 0 else final[i-1];
        final := final + [if a[i] > k - prev then a[i] else k - prev];
    }
    additionalWalks := sum(final) - sum(a);
    finalSchedule := final;
}
// </vc-code>

