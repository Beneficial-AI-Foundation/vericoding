//ATOM

//Now do the same but with a loop from right to left
predicate SumMaxToRight2(v:array<int>,j:int,i:int,s:int)//maximum sum stuck to the right
reads v
requires 0<=j<=i<v.Length
{(forall l,ss {:induction l}::j<=l<=i && ss==i+1 ==> Sum2(v,l,ss)<=s)}


//ATOM


function Sum2(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
{
  if (i==j) then 0
  else v[i]+Sum2(v,i+1,j)
}


// SPEC

method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) && SumMaxToRight2(v,0,i,s)
//Implement and verify
{
}
