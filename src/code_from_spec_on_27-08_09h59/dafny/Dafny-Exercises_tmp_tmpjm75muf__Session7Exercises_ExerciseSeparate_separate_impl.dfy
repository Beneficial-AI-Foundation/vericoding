predicate strictNegative(v:array<int>,i:int,j:int)
reads v
requires 0<=i<=j<=v.Length
{forall u | i<=u<j :: v[u]<0}

predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

predicate isPermutation(s:seq<int>, t:seq<int>)
{multiset(s)==multiset(t)}

/**
returns an index st new array is a permutation of the old array
positive first and then strictnegative, i is the firs neg or len if not any */

// <vc-helpers>
lemma MultisetSwapPreservation(s: seq<int>, i: int, j: int)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures multiset(s) == multiset(s[i := s[j]][j := s[i]])
{
  var s' := s[i := s[j]][j := s[i]];
  assert multiset(s) == multiset(s');
}

lemma PositiveExtension(s: seq<int>, val: int)
  requires positive(s)
  requires val >= 0
  ensures positive(s + [val])
{
}

lemma StrictNegativeExtension(v: array<int>, i: int, val: int)
  requires 0 <= i < v.Length
  requires val < 0
  ensures strictNegative(v, i, i+1) <==> v[i] < 0
{
}

lemma PositivePreservationSwap(v: array<int>, i: int, j: int)
  requires 0 <= i < v.Length && 0 <= j < v.Length
  requires i < j
  requires positive(v[0..i])
  requires v[i] >= 0
  ensures positive(v[0..i+1])
{
  assert v[0..i+1][i] == v[i];
  assert v[i] >= 0;
  assert forall k :: 0 <= k < i ==> v[0..i+1][k] == v[0..i][k] >= 0;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method separate(v:array<int>) returns (i:int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v,i,v.Length)
ensures isPermutation(v[0..v.Length], old(v[0..v.Length]))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  i := 0;
  var j := v.Length - 1;
  
  while i <= j
    invariant 0 <= i <= j + 1 <= v.Length
    invariant positive(v[0..i])
    invariant strictNegative(v, j+1, v.Length)
    invariant isPermutation(v[0..v.Length], old(v[0..v.Length]))
    decreases j - i + 1
  {
    if v[i] >= 0 {
      i := i + 1;
    } else if v[j] < 0 {
      j := j - 1;
    } else {
      assert v[i] < 0 && v[j] >= 0;
      v[i], v[j] := v[j], v[i];
      assert v[i] >= 0;
      PositivePreservationSwap(v, i, j);
      i := i + 1;
      j := j - 1;
    }
  }
}
// </vc-code>
