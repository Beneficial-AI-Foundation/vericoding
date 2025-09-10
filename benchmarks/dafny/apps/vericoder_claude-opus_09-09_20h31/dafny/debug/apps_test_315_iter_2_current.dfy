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
lemma SliceAppend(s: seq<int>, x: int)
    requires |s| > 0
    ensures (s + [x])[1..] == s[1..] + [x]
{
    // This lemma proves that slicing after appending preserves the append structure
}

lemma SumAppend(s: seq<int>, x: int)
    ensures sum(s + [x]) == sum(s) + x
{
    if |s| == 0 {
        assert s + [x] == [x];
    } else {
        calc {
            sum(s + [x]);
            == (s + [x])[0] + sum((s + [x])[1..]);
            == { assert (s + [x])[0] == s[0]; }
            s[0] + sum((s + [x])[1..]);
            == { SliceAppend(s, x); }
            s[0] + sum(s[1..] + [x]);
            == { SumAppend(s[1..], x); }
            s[0] + sum(s[1..]) + x;
            == sum(s) + x;
        }
    }
}

lemma SumDifference(original: seq<int>, modified: seq<int>)
    requires |original| == |modified|
    ensures sum(modified) - sum(original) == if |original| == 0 then 0 else (modified[0] - original[0]) + (sum(modified[1..]) - sum(original[1..]))
{
    if |original| == 0 {
        assert sum(modified) == 0;
        assert sum(original) == 0;
    } else {
        calc {
            sum(modified) - sum(original);
            == (modified[0] + sum(modified[1..])) - (original[0] + sum(original[1..]));
            == (modified[0] - original[0]) + (sum(modified[1..]) - sum(original[1..]));
        }
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
    finalSchedule := [];
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |finalSchedule| == i
        invariant forall j :: 0 <= j < i ==> finalSchedule[j] >= a[j]
        invariant forall j :: 0 <= j < i - 1 ==> finalSchedule[j] + finalSchedule[j + 1] >= k
    {
        if i == 0 {
            finalSchedule := finalSchedule + [a[0]];
        } else {
            var needed := k - finalSchedule[
// </vc-code>

