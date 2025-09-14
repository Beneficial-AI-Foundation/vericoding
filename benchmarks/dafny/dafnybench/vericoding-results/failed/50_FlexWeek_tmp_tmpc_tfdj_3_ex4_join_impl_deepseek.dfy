

// <vc-helpers>
lemma Lemma_SliceConcat(a: seq<int>, b: seq<int>)
  ensures a + b == a[..] + b[..]
{
}

lemma Lemma_MultisetConcat(a: seq<int>, b: seq<int>)
  ensures multiset(a[..] + b[..]) == multiset(a + b)
{
}

lemma Lemma_MultisetCombine(a: seq<int>, b: seq<int>)
  ensures multiset(a[..]) + multiset(b[..]) == multiset(a + b)
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
    invariant i == a.Length
    invariant forall k :: 0 <= k < a.Length ==> c[k] == a[k]
    invariant forall k :: 0 <= k < j ==> c[a.Length + k] == b[k]
  {
    c[a.Length + j] := b[j];
    j := j + 1;
  }
  
  // Prove the forall condition with explicit parentheses
  assert forall i_2, j_2 ::
    (a.Length <= i_2 < c.Length) &&
    (0 <= j_2 < b.Length) && 
    (i_2 - j_2 == a.Length) ==> 
    c[i_2] == b[j_2];
  
  // Prove sequence equality
  assert c[..] == a[..] + b[..] by {
    Lemma_SliceConcat(a[..], b[..]);
  }
  
  // Prove multiset properties
  assert multiset(c[..]) == multiset(a[..] + b[..]) by {
    Lemma_MultisetConcat(a[..], b[..]);
  }
  
  assert multiset(a[..]) + multiset(b[..]) == multiset(c[..]) by {
    Lemma_MultisetCombine(a[..], b[..]);
    Lemma_MultisetConcat(a[..], b[..]);
  }
}
// </vc-code>

