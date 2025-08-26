method separate(v:array<int>) returns (i:int)
modifies v
ensures 0<=i<=v.Length
ensures positive(v[0..i]) && strictNegative(v,i,v.Length)
ensures isPermutation(v[0..v.Length], old(v[0..v.Length]))
// </vc-spec>
// <vc-code>
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
      v[i], v[j] := v[j], v[i];
      i := i + 1;
    }
    j := j + 1;
  }
}
// </vc-code>
// <vc-helpers>
predicate positive(s: seq<int>)
{
  forall k :: 0 <= k < |s| ==> s[k] >= 0
}

predicate strictNegative(v: array<int>, i: int, j: int)
  reads v
  requires 0 <= i <= j <= v.Length
{
  forall k :: i <= k < j ==> v[k] < 0
}

predicate isPermutation(s1: seq<int>, s2: seq<int>)
{
  multiset(s1) == multiset(s2)
}
// </vc-helpers>