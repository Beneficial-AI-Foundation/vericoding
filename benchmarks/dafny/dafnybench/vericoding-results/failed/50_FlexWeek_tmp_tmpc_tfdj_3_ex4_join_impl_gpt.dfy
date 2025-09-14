

// <vc-helpers>
lemma SeqEqFromChunks(a: array<int>, b: array<int>, c: array<int>)
  requires a != null && b != null && c != null
  requires c.Length == a.Length + b.Length
  requires forall k :: 0 <= k < a.Length ==> c[k] == a[k]
  requires forall k :: 0 <= k < b.Length ==> c[a.Length + k] == b[k]
  ensures c[..] == a[..] + b[..]
{
  assert c[..].Length == (a[..] + b[..]).Length;
  assert forall i :: 0 <= i < c.Length ==> c[..][i] == (a[..] + b[..])[i] by
  {
    if i < a.Length {
      assert c[..][i] == c[i];
      assert (a[..] + b[..])[i] == a[i];
      assert c[i] == a[i];
    } else {
      var j := i - a.Length;
      assert 0 <= j;
      assert i < a.Length + b.Length;
      assert j < b.Length;
      assert c[..][i] == c[i];
      assert (a[..] + b[..])[i] == b[j];
      assert c[i] == c[a.Length + j];
      assert c[a.Length + j] == b[j];
    }
    assert c[..][i] == (a[..] + b[..])[i];
  }
  assert c[..] == a[..] + b[..];
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
    invariant c.Length == a.Length + b.Length
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
    decreases a.Length - i
  {
    c[i] := a[i];
    i := i + 1;
  }

  var j := 0;
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant c.Length == a.Length + b.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: 0 <= k < j ==> c[a.Length + k] == b[k]
    decreases b.Length - j
  {
    c[a.Length + j] := b[j];
    j := j + 1;
  }

  SeqEqFromChunks(a, b, c);
}
// </vc-code>

