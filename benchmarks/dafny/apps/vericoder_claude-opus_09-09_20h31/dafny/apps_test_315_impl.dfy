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

lemma SumGeq(s1: seq<int>, s2: seq<int>)
    requires |s1| == |s2|
    requires forall i :: 0 <= i < |s1| ==> s1[i] >= s2[i]
    ensures sum(s1) >= sum(s2)
{
    if |s1| == 0 {
        assert sum(s1) == 0 && sum(s2) == 0;
    } else {
        assert s1[0] >= s2[0];
        assert forall i :: 0 <= i < |s1[1..]| ==> s1[1..][i] >= s2[1..][i];
        SumGeq(s1[1..], s2[1..]);
        assert sum(s1[1..]) >= sum(s2[1..]);
        calc {
            sum(s1);
            == s1[0] + sum(s1[1..]);
            >= s2[0] + sum(s2[1..]);
            == sum(s2);
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
        invariant sum(finalSchedule[..i]) >= sum(a[..i])
    {
        if i == 0 {
            finalSchedule := finalSchedule + [a[0]];
            assert finalSchedule[0] >= a[0];
            assert sum(finalSchedule[..1]) >= sum(a[..1]);
        } else {
            var needed := k - finalSchedule[i - 1];
            var walks := if needed > a[i] then needed else a[i];
            finalSchedule := finalSchedule + [walks];
            assert walks >= a[i];
            assert finalSchedule[i] >= a[i];
            
            assert forall j {:trigger finalSchedule[..i+1][j]} :: 0 <= j < i ==> finalSchedule[..i+1][j] >= a[..i+1][j];
            assert finalSchedule[..i+1][i] >= a[..i+1][i];
            SumGeq(finalSchedule[..i+1], a[..i+1]);
            assert sum(finalSchedule[..i+1]) >= sum(a[..i+1]);
        }
        i := i + 1;
    }
    
    assert |finalSchedule| == n;
    assert forall j :: 0 <= j < n ==> finalSchedule[j] >= a[j];
    SumGeq(finalSchedule, a);
    assert sum(finalSchedule) >= sum(a);
    
    additionalWalks := sum(finalSchedule) - sum(a);
    assert additionalWalks >= 0;
}
// </vc-code>

