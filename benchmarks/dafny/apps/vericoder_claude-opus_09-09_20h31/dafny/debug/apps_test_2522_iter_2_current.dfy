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
lemma RotationProperties(original: seq<int>, k: int)
    requires 0 <= k < |original|
    ensures |original| == |original[k..] + original[..k]|
    ensures multiset(original) == multiset(original[k..] + original[..k])
{
    var rotated := original[k..] + original[..k];
    assert |rotated| == |original[k..]| + |original[..k]| == (|original| - k) + k == |original|;
    
    // Prove multiset equality by showing each element appears the same number of times
    var i := 0;
    while i < |original|
        invariant 0 <= i <= |original|
    {
        if i < k {
            assert original[i] == rotated[|original| - k + i];
        } else {
            assert original[i] == rotated[i - k];
        }
        i := i + 1;
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
    var k := 0;
    var found := false;
    var rotated_b: seq<int> := [];
    
    while k < n && !found
        invariant 0 <= k <= n
        invariant found ==> |rotated_b| == n
        invariant found ==> IsRotation(b, rotated_b)
        invariant found ==> ValidReordering(a, rotated_b)
    {
        // Create the rotation first
        var candidate := b[k..] + b[..k];
        RotationProperties(b, k);
        assert |candidate| == n;
        assert multiset(b) == multiset(candidate);
        
        // Check if this rotation is valid
        var valid := true;
        var i := 0;
        
        while i < n && valid
            invariant 0 <= i <= n
            invariant valid ==> (forall j :: 0 <= j < i ==> a[j] != candidate[j])
            invariant candidate == b[k..] + b[..k]
        {
            if a[i] == candidate[i] {
                valid := false;
            }
            i := i + 1;
        }
        
        if valid {
            rotated_b := candidate;
            found := true;
            assert ValidReordering(a, rotated_b);
            assert IsRotation(b, rotated_b);
        }
        
        k := k + 1;
    }
    
    if found {
        result := (true, rotated_b);
    } else {
        result := (false, []);
    }
}
// </vc-code>

