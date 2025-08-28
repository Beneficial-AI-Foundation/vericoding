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
lemma PermutationTransitivity(a: seq<int>, b: seq<int>, c: seq<int>)
  ensures multiset(a) == multiset(b) && multiset(b) == multiset(c) ==> multiset(a) == multiset(c)
{
}

lemma PermutationAppend(s1: seq<int>, s2: seq<int>, t1: seq<int>, t2: seq<int>)
  ensures multiset(s1 + s2) == multiset(t1 + t2) ==> multiset(s1) == multiset(t1) && multiset(s2) == multiset(t2) ==> multiset(s1 + s2) == multiset(t1 + t2)
{
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
method Separate(v: array<int>) returns (i: int)
  modifies v
  ensures 0 <= i <= v.Length
  ensures positive(v[0..i]) && strictNegative(v, i, v.Length)
  ensures isPermutation(v[0..v.Length], old(v[0..v.Length]))
{
  i := 0;
  var j := 0;
  while j < v.Length
    invariant 0 <= i <= j <= v.Length
    invariant positive(v[0..i])
    invariant strictNegative(v, i, j)
    invariant isPermutation(v[0..v.Length], old(v[0..v.Length]))
  {
    if v[j] >= 0 {
      if i != j {
        v[i], v[j] := v[j], v[i];
      }
      i := i + 1;
    }
    j := j + 1;
  }
}
// </vc-code>
