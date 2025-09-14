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
method CheckCondition(a: seq<int>, b_rot: seq<int>) returns (ok: bool)
    requires |a| == |b_rot|
    ensures ok == ValidReordering(a, b_rot)
{
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant forall j :: 0 <= j < i ==> a[j] != b_rot[j]
    {
        if a[i] == b_rot[i] {
            return false;
        }
        i := i + 1;
    }
    return true;
}

lemma RotationPreservesMultiset(original: seq<int>, k: int)
    requires 0 <= k <= |original|
    ensures multiset(original) == multiset(original[k..] + original[..k])
{
    calc {
        multiset(original);
        == { assert original == original[..k] + original[k..]; }
        multiset(original[..k] + original[k..]);
        == 
        multiset(original[..k]) + multiset(original[k..]);
        == 
        multiset(original[k..]) + multiset(original[..k]);
        == 
        multiset(original[k..] + original[..k]);
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
    for k := 0 to n-1
    {
        var rotated := b[k..] + b[..k];
        RotationPreservesMultiset(b, k);
        var ok := CheckCondition(a, rotated);
        if ok {
            return (true, rotated);
        }
    }
    return (false, []);
}
// </vc-code>

