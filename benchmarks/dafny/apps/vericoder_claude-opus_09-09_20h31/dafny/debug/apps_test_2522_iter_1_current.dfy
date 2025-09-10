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
}

lemma ValidReorderingCheck(a: seq<int>, b: seq<int>, k: int) returns (isValid: bool)
    requires |a| == |b| && |a| >= 1
    requires 0 <= k < |a|
    ensures isValid == (forall i :: 0 <= i < |a| ==> a[i] != b[(i + k) % |a|])
{
    isValid := true;
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant isValid == (forall j :: 0 <= j < i ==> a[j] != b[(j + k) % |a|])
    {
        if a[i] == b[(i + k) % |a|] {
            isValid := false;
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
    var rotated_b := [];
    
    while k < n && !found
        invariant 0 <= k <= n
        invariant !found
    {
        // Check if rotation by k works
        var valid := true;
        var i := 0;
        
        while i < n && valid
            invariant 0 <= i <= n
            invariant valid ==> (forall j :: 0 <= j < i ==> a[j] != b[(j + k) % n])
        {
            if a[i] == b[(i + k) % n] {
                valid := false;
            }
            i := i + 1;
        }
        
        if valid {
            // Create the rotation
            rotated_b := b[k..] + b[..k];
            found := true;
            
            // Verify properties
            RotationProperties(b, k);
            assert |rotated_b| == n;
            assert IsRotation(b, rotated_b);
            assert IsReorderingOf(b, rotated_b);
            
            // Verify ValidReordering
            assert forall i :: 0 <= i < n ==> rotated_b[i] == b[(i + k) % n];
            assert forall i :: 0 <= i < n ==> a[i] != rotated_b[i];
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

