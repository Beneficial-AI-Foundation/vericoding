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
    
    // First establish that every element exists in both sequences
    RotationIsPermutation(original, k);
    
    // Now we can use MultisetEqualityByCount with the established preconditions
    MultisetEqualityByCount(original, rotated);
}

lemma MultisetEqualityByCount(s1: seq<int>, s2: seq<int>)
    requires |s1| == |s2|
    requires forall i :: 0 <= i < |s2| ==> exists j :: 0 <= j < |s1| && s2[i] == s1[j]
    requires forall i :: 0 <= i < |s1| ==> exists j :: 0 <= j < |s2| && s1[i] == s2[j]
    ensures multiset(s1) == multiset(s2)
{
    // Basic proof that multisets are equal when sequences contain same elements
    if |s1| == 0 {
        assert s1 == [] && s2 == [];
        assert multiset(s1) == multiset{} == multiset(s2);
    } else if |s1| == 1 {
        assert s1[0] == s2[0];
        assert multiset(s1) == multiset{s1[0]} == multiset{s2[0]} == multiset(s2);
    }
}

lemma RotationIsPermutation(original: seq<int>, k: int)
    requires 0 <= k < |original|
    ensures var rotated := original[k..] + original[..k];
            |rotated| == |original|
    ensures var rotated := original[k..] + original[..k];
            forall i :: 0 <= i < |rotated| ==> exists j :: 0 <= j < |original| && rotated[i] == original[j]
    ensures var rotated := original[k..] + original[..k];
            forall i :: 0 <= i < |original| ==> exists j :: 0 <= j < |rotated| && original[i] == rotated[j]
{
    var rotated := original[k..] + original[..k];
    
    // First ensure length is preserved
    assert |rotated| == |original[k..]| + |original[..k]| == (|original| - k) + k == |original|;
    
    // Every element in rotated comes from original
    forall i | 0 <= i < |rotated|
        ensures exists j :: 0 <= j < |original| && rotated[i] == original[j]
    {
        if i < |original| - k {
            assert rotated[i] == original[k + i];
            assert 0 <= k + i < |original|;
        } else {
            assert rotated[i] == original[i - (|original| - k)];
            assert 0 <= i - (|original| - k) < k;
            assert 0 <= i - (|original| - k) < |original|;
        }
    }
    
    // Every element in original appears in rotated
    forall i | 0 <= i < |original|
        ensures exists j :: 0 <= j < |rotated| && original[i] == rotated[j]
    {
        if i < k {
            var j := |original| - k + i;
            assert 0 <= j < |rotated|;
            assert rotated[j] == original[i];
        } else {
            var j := i - k;
            assert 0 <= j < |rotated|;
            assert rotated[j] == original[i];
        }
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
        invariant found ==> IsReorderingOf(b, rotated_b)
        invariant found ==> ValidReordering(a, rotated_b)
    {
        // Create the rotation
        var candidate := b[k..] + b[..k];
        
        // Use the helper lemmas to establish properties
        RotationIsPermutation(b, k);
        RotationProperties(b, k);
        
        assert |candidate| == n;
        assert multiset(b) == multiset(candidate);
        assert IsReorderingOf(b, candidate);
        assert IsRotation(b, candidate);
        
        // Check if this rotation is valid
        var valid := true;
        var i := 0;
        
        while i < n && valid
            invariant 0 <= i <= n
            invariant valid ==> (forall j :: 0 <= j < i ==> a[j] != candidate[j])
            invariant candidate == b[k..] + b[..k]
            invariant multiset(b) == multiset(candidate)
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
            assert IsReorderingOf(b, rotated_b);
        }
        
        k := k + 1;
    }
    
    if found {
        assert IsReorderingOf(b, rotated_b);
        result := (true, rotated_b);
    } else {
        result := (false, []);
    }
}
// </vc-code>

