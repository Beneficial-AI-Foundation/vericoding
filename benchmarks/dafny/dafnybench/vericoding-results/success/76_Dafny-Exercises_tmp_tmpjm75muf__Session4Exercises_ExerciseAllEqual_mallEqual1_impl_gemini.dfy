// <vc-preamble>
predicate allEqual(s:seq<int>)
{forall i,j::0<=i<|s| && 0<=j<|s| ==> s[i]==s[j] }
// </vc-preamble>

// <vc-helpers>
lemma AllEqualToConstantImpliesAllEqual(s: seq<int>, c: int)
  requires forall i :: 0 <= i < |s| ==> s[i] == c
  ensures allEqual(s)
{}
// </vc-helpers>

// <vc-spec>
method mallEqual1(v:array<int>) returns (b:bool)
ensures b==allEqual(v[0..v.Length])
// </vc-spec>
// <vc-code>
{
  if v.Length <= 1 {
    b := true;
    return;
  }

  var i := 1;
  while i < v.Length
    invariant 1 <= i <= v.Length
    invariant forall k :: 1 <= k < i ==> v[k] == v[0]
  {
    if v[i] != v[0] {
      b := false;
      return;
    }
    i := i + 1;
  }

  AllEqualToConstantImpliesAllEqual(v[0..v.Length], v[0]);
  b := true;
}
// </vc-code>
