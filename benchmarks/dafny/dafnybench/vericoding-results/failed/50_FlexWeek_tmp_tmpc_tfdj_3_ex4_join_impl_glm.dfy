

// <vc-helpers>
//
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
    invariant multiset(c[0..i]) == multiset(a[0..i])
  {
    c[i] := a[i];
    i := i + 1;
  }
  var j := 0;
  i := a.Length;
  while j < b.Length
    invariant a.Length <= i <= a.Length + b.Length
    invariant j == i - a.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: a.Length <= k < i ==> c[k] == b[k - a.Length]
    invariant multiset(c[0..i]) == multiset(a[0..a.Length]) + multiset(b[0..j])
  {
    c[i] := b[j];
    i := i + 1;
    j := j + 1;
  }
  return c;
}
// </vc-code>

