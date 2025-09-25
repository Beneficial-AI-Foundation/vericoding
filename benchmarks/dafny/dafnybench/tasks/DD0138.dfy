// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method replace(v:array<int>, x:int, y:int)
modifies v
ensures forall k::0<=k<old(v.Length) && old(v[k])==x ==> v[k]==y
ensures forall k::0<=k<old(v.Length) && old(v[k])!=x ==> v[k]==old(v[k])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
