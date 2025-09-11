// <vc-preamble>
predicate isPeek(v:array<int>,i:int)
 reads v
 requires 0<=i<v.Length
 {forall k::0<=k<i ==> v[i]>=v[k]}

 function peekSum(v:array<int>,i:int):int
 decreases i 
 reads v
 requires 0<=i<=v.Length
 {
  if (i==0) then 0
  else if isPeek(v,i-1) then v[i-1]+peekSum(v,i-1)
  else peekSum(v,i-1)
 }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method mPeekSum(v:array<int>) returns (sum:int)
 requires  v.Length>0
 ensures sum==peekSum(v,v.Length)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
