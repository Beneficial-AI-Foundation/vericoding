// <vc-preamble>
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mfirstNegative(v:array<int>) returns (b:bool, i:int)
ensures b <==> exists k::0<=k<v.Length && v[k]<0
ensures b ==> 0<=i<v.Length && v[i]<0 && positive(v[0..i])
// </vc-spec>
// <vc-code>
{
  i := 0; // default value, doesn't matter if b ends up false
  b := false;
  var j := 0;
  while j < v.Length
    invariant 0 <= j <= v.Length
    invariant b == false
    invariant positive(v[0..j])
  {
    if v[j] < 0 {
      b := true;
      i := j;
      return;
    }
    j := j + 1;
  }
}
// </vc-code>
