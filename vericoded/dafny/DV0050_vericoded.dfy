// <vc-preamble>
predicate IsSorted(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate MultisetEquiv(s1: seq<int>, s2: seq<int>)
{
    multiset(s1) == multiset(s2)
}
method MergeSortedAux(a: seq<int>, b: seq<int>) returns (result: seq<int>)
{
    assume {:axiom} false;
    result := [];
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove multiset equality for sequence slicing */
lemma MultisetSliceLemma(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures multiset([s[i]]) + multiset(s[i+1..]) == multiset(s[i..])
{
  assert s[i..] == [s[i]] + s[i+1..];
}
// </vc-helpers>

// <vc-spec>
method MergeSorted(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires IsSorted(a)
    requires IsSorted(b)
    ensures IsSorted(result)
    ensures MultisetEquiv(result, a + b)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Use lemma to prove multiset assertions */
  var i := 0;
  var j := 0;
  result := [];
  
  while i < |a| || j < |b|
    invariant 0 <= i <= |a|
    invariant 0 <= j <= |b|
    invariant IsSorted(result)
    invariant forall k :: 0 <= k < |result| ==> 
      (forall m :: i <= m < |a| ==> result[k] <= a[m]) &&
      (forall n :: j <= n < |b| ==> result[k] <= b[n])
    invariant multiset(result) + multiset(a[i..]) + multiset(b[j..]) == multiset(a) + multiset(b)
    decreases |a| - i + |b| - j
  {
    if i == |a| {
      assert a[i..] == [];
      assert multiset(result + [b[j]]) + multiset(a[i..]) + multiset(b[j+1..]) == multiset(result) + multiset([b[j]]) + multiset(a[i..]) + multiset(b[j+1..]);
      MultisetSliceLemma(b, j);
      result := result + [b[j]];
      j := j + 1;
    } else if j == |b| {
      assert b[j..] == [];
      assert multiset(result + [a[i]]) + multiset(a[i+1..]) + multiset(b[j..]) == multiset(result) + multiset([a[i]]) + multiset(a[i+1..]) + multiset(b[j..]);
      MultisetSliceLemma(a, i);
      result := result + [a[i]];
      i := i + 1;
    } else if a[i] <= b[j] {
      MultisetSliceLemma(a, i);
      result := result + [a[i]];
      i := i + 1;
    } else {
      MultisetSliceLemma(b, j);
      result := result + [b[j]];
      j := j + 1;
    }
  }
  assert i == |a| && j == |b|;
  assert a[i..] == [] && b[j..] == [];
  assert multiset(result) == multiset(a) + multiset(b);
}
// </vc-code>
