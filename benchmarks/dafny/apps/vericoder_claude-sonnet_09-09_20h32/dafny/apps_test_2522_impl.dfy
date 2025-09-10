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
lemma MultisetSliceProperty<T>(s: seq<T>, k: int)
    requires 0 <= k <= |s|
    ensures multiset(s) == multiset(s[k..]) + multiset(s[..k])
{
    if k == 0 {
        assert s[k..] == s;
        assert s[..k] == [];
        assert multiset(s[..k]) == multiset{};
    } else if k == |s| {
        assert s[k..] == [];
        assert s[..k] == s;
        assert multiset(s[k..]) == multiset{};
    } else {
        assert s == s[..k] + s[k..];
        assert multiset(s[..k] + s[k..]) == multiset(s[..k]) + multiset(s[k..]);
    }
}

lemma RotationIsReordering(original: seq<int>, k: int)
    requires 0 <= k < |original|
    ensures IsReorderingOf(original, original[k..] + original[..k])
{
    var rotated := original[k..] + original[..k];
    MultisetSliceProperty(original, k);
    assert multiset(original) == multiset(original[k..]) + multiset(original[..k]);
    assert multiset(rotated) == multiset(original[k..] + original[..k]);
    assert multiset(original[k..] + original[..k]) == multiset(original[k..]) + multiset(original[..k]);
}

lemma RotationIsRotation(original: seq<int>, k: int)
    requires 0 <= k < |original|
    ensures IsRotation(original, original[k..] + original[..k])
{
    var rotated := original[k..] + original[..k];
    assert rotated == original[k..] + original[..k];
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
    var k := 0;
    while k < n
        invariant 0 <= k <= n
    {
        var rotated := b[k..] + b[..k];
        assert |rotated| == n;
        
        var valid := true;
        var i := 0;
        while i < n && valid
            invariant 0 <= i <= n
            invariant valid ==> forall j :: 0 <= j < i ==> a[j] != rotated[j]
        {
            if a[i] == rotated[i] {
                valid := false;
            }
            i := i + 1;
        }
        
        if valid {
            RotationIsReordering(b, k);
            RotationIsRotation(b, k);
            return (true, rotated);
        }
        
        k := k + 1;
    }
    
    return (false, []);
}
// </vc-code>

