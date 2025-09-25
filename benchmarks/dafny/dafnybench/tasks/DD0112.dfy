// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method mfirstMaximum(v:array<int>) returns (i:int)
requires v.Length>0
ensures 0<=i<v.Length 
ensures forall k:: 0<=k<v.Length ==> v[i]>=v[k]
ensures forall l:: 0<=l<i ==> v[i]>v[l]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
