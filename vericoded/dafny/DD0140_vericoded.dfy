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
lemma swapPreservesMultiset(s: seq<int>, i: int, j: int) returns (s': seq<int>)
  requires 0 <= i < |s| && 0 <= j < |s|
  ensures |s'| == |s|
  ensures multiset(s) == multiset(s')
  ensures s'[i] == s[j] && s'[j] == s[i]
  ensures forall k :: 0 <= k < |s| && k != i && k != j ==> s'[k] == s[k]
{
  s' := s[i := s[j]][j := s[i]];
}
// </vc-helpers>

// <vc-spec>
method separate(v:array<int>) returns (i:int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v,i,v.Length)
ensures isPermutation(v[0..v.Length], old(v[0..v.Length]))
// </vc-spec>
// <vc-code>
{
  i := 0;
  var j := v.Length - 1;
  
  while i <= j
    invariant 0 <= i <= j + 1 <= v.Length
    invariant positive(v[0..i])
    invariant strictNegative(v, j + 1, v.Length)
    invariant multiset(v[0..v.Length]) == multiset(old(v[0..v.Length]))
    decreases j - i
  {
    if v[i] >= 0 {
      i := i + 1;
    } else if v[j] < 0 {
      j := j - 1;
    } else {
      var temp := v[i];
      v[i] := v[j];
      v[j] := temp;
      i := i + 1;
      j := j - 1;
    }
  }
}
// </vc-code>

