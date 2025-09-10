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
function rotate(s: seq<int>, k: int): seq<int>
    requires 0 <= k <= |s|
    ensures |rotate(s, k)| == |s|
    ensures multiset(rotate(s, k)) == multiset(s)
{
    if k == 0 then s else s[k..] + s[..k]
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
    var reordered_b: seq<int>;
    var found := false;

    // Iterate through all possible rotations of b
    var k := 0;
    while k < n
        invariant 0 <= k <= n
        invariant !found ==> (forall j :: 0 <= j < k ==> !(IsReorderingOf(b, rotate(b, j)) && ValidReordering(a, rotate(b, j))))
        invariant found ==> (IsReorderingOf(b, reordered_b) && ValidReordering(a, reordered_b) && IsRotation(b, reordered_b))
    {
        reordered_b := rotate(b, k);
        var is_valid_reordering := true;

        // Check if `reordered_b` is a valid reordering of `a`
        for i := 0 to n - 1
            invariant 0 <= i <= n
            invariant is_valid_reordering ==> (forall j :: 0 <= j < i ==> a[j] != reordered_b[j])
        {
            if a[i] == reordered_b[i] {
                is_valid_reordering := false;
                break;
            }
        }

        if is_valid_reordering {
            // Also need to ensure it's a reordering of b (i.e., permutation)
            // Since it's a rotation, it's guaranteed to be a permutation.
            // And IsReorderingOf requires multiset equality.
            // A rotation preserves the multiset of elements.
            // A rotation also preserves the length.
            assert IsReorderingOf(b, reordered_b); // This is guaranteed by the postcondition of rotate
            assert IsRotation(b, reordered_b);     // This is guaranteed by construction
            found := true;
            break;
        }
        k := k + 1;
    }

    if found {
        return (true, reordered_b);
    } else {
        return (false, []);
    }
}
// </vc-code>

