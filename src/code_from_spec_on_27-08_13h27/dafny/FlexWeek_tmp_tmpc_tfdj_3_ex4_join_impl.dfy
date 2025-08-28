// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
method Join(a: array<int>, b: array<int>) returns (c: array<int>)
  ensures a[..] + b[..] == c[..]
  ensures multiset(a[..] + b[..]) == multiset(c[..])
  ensures multiset(a[..]) + multiset(b[..]) == multiset(c[..])
  ensures a.Length + b.Length == c.Length
  ensures forall i :: 0 <= i < a.Length ==> c[i] == a[i]
  ensures forall i_2, j_2 :: a.Length <= i_2 < c.Length && 0 <= j_2 < b.Length && i_2 - j_2 == a.Length ==> c[i_2] == b[j_2]
{
  c := new int[a.Length + b.Length];
  var i := 0;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> c[k] == a[k]
  {
    c[i] := a[i];
    i := i + 1;
  }
  
  i := 0;
  while i < b.Length
    invariant 0 <= i <= b.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: 0 <= k < i ==> c[a.Length + k] == b[k]
  {
    c[a.Length + i] := b[i];
    i := i + 1;
  }
}
// </vc-code>
