predicate ValidInput(n: int, a: seq<int>, b: seq<int>)
{
    |a| == n && |b| == n && n >= 1 &&
    (forall i :: 0 <= i < n-1 ==> a[i] <= a[i+1]) &&
    (forall i :: 0 <= i < n-1 ==> b[i] <= b[i+1])
}

predicate ValidReordering(a: seq<int>, reordered_b: seq<int>)
    requires |a| == |reordered_b|
{
    forall i :: 0 <= i < |a| ==> a[i] != reordered_b[i]
}

predicate IsReorderingOf(original: seq<int>, reordered: seq<int>)
{
    |original| == |reordered| && multiset(original) == multiset(reordered)
}

predicate IsRotation(original: seq<int>, rotated: seq<int>)
{
    |original| == |rotated| && 
    (exists k :: 0 <= k < |original| && rotated == original[k..] + original[..k])
}

// <vc-helpers>
lemma RotationPreservesMultiset(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures multiset(s[k..] + s[..k]) == multiset(s)
{
  calc {
    multiset(s);
    == { assert s == s[..k] + s[k..]; } multiset(s[..k] + s[k..]);
    == multiset(s[..k]) + multiset(s[k..]);
    == multiset(s[k..]) + multiset(s[..k]);
}
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>, b: seq<int>) returns (result: (bool, seq<int>))
    requires ValidInput(n, a, b)
    ensures result.0 ==> |result.1| == n
    ensures result.0 ==> IsReorderingOf(b, result.1)
    ensures result.0 ==> ValidReordering(a, result.1)
    ensures !result.0 ==> result.1 == []
    ensures result.0 ==> IsRotation(b, result.1)
// </vc-spec>
// <vc-code>
{
    for k := 0 to n - 1 {
        var rotated := b[k..] + b[..k];
        RotationPreservesMultiset(b, k);
        if forall i :: 0 <= i < n ==> rotated[i] != a[i] {
            return (true, rotated);
        }
    }
    return (false, []);
}
// </vc-code>

