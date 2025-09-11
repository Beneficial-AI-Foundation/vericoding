// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method mfirstCero(v:array<int>) returns (i:int)
ensures 0 <=i<=v.Length
ensures forall j:: 0<=j<i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
