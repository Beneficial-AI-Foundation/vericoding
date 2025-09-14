

// <vc-helpers>
lemma multiset_concatenation_property<T>(s1: seq<T>, s2: seq<T>)
  ensures multiset(s1 + s2) == multiset(s1) + multiset(s2)
{
}

lemma array_copy_preserves_sequence(src: array<int>, dest: array<int>, src_start: int, dest_start: int, length: int)
  requires 0 <= src_start <= src_start + length <= src.Length
  requires 0 <= dest_start <= dest_start + length <= dest.Length
  requires forall i :: 0 <= i < length ==> dest[dest_start + i] == src[src_start + i]
  ensures dest[dest_start..dest_start + length] == src[src_start..src_start + length]
{
}

lemma sequence_concatenation_property(a: seq<int>, b: seq<int>, c: seq<int>)
  requires c == a + b
  ensures c[..] == a + b
{
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
  {
    c[i] := a[i];
    i := i + 1;
  }
  
  var j := 0;
  while j < b.Length
    invariant 0 <= j <= b.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: 0 <= k < j ==> c[a.Length + k] == b[k]
  {
    c[a.Length + j] := b[j];
    j := j + 1;
  }
  
  assert forall k :: 0 <= k < a.Length ==> c[k] == a[k];
  assert forall k :: 0 <= k < b.Length ==> c[a.Length + k] == b[k];
  
  assert c[..a.Length] == a[..];
  assert c[a.Length..] == b[..];
  assert c[..] == c[..a.Length] + c[a.Length..];
  
  multiset_concatenation_property(a[..], b[..]);
}
// </vc-code>

