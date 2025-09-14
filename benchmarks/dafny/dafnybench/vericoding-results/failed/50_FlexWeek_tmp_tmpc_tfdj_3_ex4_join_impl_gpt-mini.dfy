

// <vc-helpers>
lemma JoinLemma(a: array<int>, b: array<int>, c: array<int>)
  requires c.Length == a.Length + b.Length
  requires forall k :: 0 <= k < a.Length ==> c[k] == a[k]
  requires forall k :: a.Length <= k < a.Length + b.Length ==> c[k] == b[k - a.Length]
  ensures forall i_2,j_2 :: a.Length <= i_2 < c.Length && 0 <= j_2 < b.Length && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2]
{
  forall i_2, j_2 | a.Length <= i_2 < c.Length && 0 <= j_2 < b.Length && i_2 - j_2 == a.Length
  {
    // From i_2 - j_2 == a.Length obtain i_2 == a.Length + j_2 and hence i_2 - a.Length == j_2
    assert i_2 == a.Length + j_2;
    assert i_2 - a.Length == j_2;
    // By the third requirement, c[i_2] == b[i_2 - a.Length]
    assert c[i_2] == b[i_2 - a.Length];
    // Replace i_2 - a.Length by j_2 to finish
    assert b[i_2 - a.Length] == b[j_2];
  }
}
// </vc-helpers>

// <vc-spec>
method join(a:array<int>,b:array<int>) returns (c:array<int>)
ensures a[..] + b[..] == c[..]
ensures multiset(a[..] + b[..]) == multiset(c[..])
ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
ensures a.Length+b.Length == c.Length

// Forall

ensures forall i :: 0<=i<a.Length ==> c[i] == a[i]
ensures forall i_2,j_2::
    a.Length <= i_2 < c.Length &&
    0<=j_2< b.Length && i_2 - j_2 == a.Length  ==> c[i_2] == b[j_2]
// </vc-spec>
// <vc-code>
{
  c := new int[a.Length + b.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
    invariant c.Length == a.Length + b.Length
  {
    c[i] := a[i];
    i := i + 1;
  }

  var j := 0;
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant c.Length == a.Length + b.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: a.Length <= k < a.Length + j ==> c[k] == b[k - a.Length]
  {
    c[a.Length + j] := b[j];
    j := j + 1;
  }

  // Prove the remaining quantified postcondition directly
  forall i_2, j_2 | a.Length <= i_2 < c.Length && 0 <= j_2 < b.Length && i_2 - j_2 == a.Length
  {
    assert i_2 == a.Length + j_2;
    assert i_2 - a.Length == j_2;
    assert c[i_2] == b[i_2 - a.Length];
    assert b[i_2 - a.Length] == b[j_2];
  }

  return c;
}
// </vc-code>

