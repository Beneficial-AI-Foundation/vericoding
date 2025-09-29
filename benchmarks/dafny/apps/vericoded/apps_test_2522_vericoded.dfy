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
function Rotate(original: seq<int>, k: int): seq<int>
  requires 0 <= k <= |original|
  ensures Rotate(original,k) == original[k..] + original[..k]
{
  original[k..] + original[..k]
}

lemma RotationPreservesMultiset(original: seq<int>, k: int)
  requires 0 <= k <= |original|
  ensures multiset(Rotate(original,k)) == multiset(original)
{
  // Rotate(original,k) == original[k..] + original[..k]
  assert Rotate(original,k) == original[k..] + original[..k];
  // original == original[..k] + original[k..]
  assert original == original[..k] + original[k..];
  // multiset respects equality
  assert multiset(original) == multiset(original[..k] + original[k..]);
  // multiset of concatenation is commutative up to multiset equality
  assert multiset(original[..k] + original[k..]) == multiset(original[k..] + original[..k]);
  assert multiset(original[k..] + original[..k]) == multiset(Rotate(original,k));
}

lemma BuildRotation(original: seq<int>, k: int)
  requires 0 <= k < |original|
  ensures IsRotation(original, Rotate(original,k))
{
  assert Rotate(original,k) == original[k..] + original[..k];
  // length equality
  assert |Rotate(original,k)| == |original[k..]| + |original[..k]| == |original|;
  // witness the existential in IsRotation
  assert exists k0 :: 0 <= k0 < |original| && Rotate(original,k) == original[k0..] + original[..k0];
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
    decreases n - k
  {
    var r := b[k..] + b[..k];
    // r is a rotation of b, so |r| == n
    assert |r| == n;
    if forall i :: 0 <= i < n ==> a[i] != r[i] {
      // prove required properties for the returned rotation
      RotationPreservesMultiset(b, k);
      BuildRotation(b, k);
      return (true, r);
    }
    k := k + 1;
  }
  return (false, []);
}
// </vc-code>

