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
  var rotated := s[k..] + s[..k];
  // Since a rotation is just a cyclic shift, the multiset remains the same.
  // Prove by case analysis on the mutlipset.
  assert |rotated| == |s| &&
         forall i :: 0 <= i < |s| ==> rotated[i] == s[(i + k) % |s|];
  // Multisets are equal because rotations preserve element counts.
  // Dafny's multiset theory handles this, but we assert for verification.
  assert multiset(rotated) == multiset(s);
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
        assert multiset(rotated) == multiset(b);
        var all_diff := true;
        for i := 0 to n - 1 {
            if rotated[i] == a[i] {
                all_diff := false;
                break;
            }
        }
        if all_diff {
            assert ValidReordering(a, rotated);
            assert IsReorderingOf(b, rotated);
            assert IsRotation(b, rotated);
            return (true, rotated);
        }
    }
    return (false, []);
}
// </vc-code>

