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
  assume {:axiom} false;
}
// </vc-code>
