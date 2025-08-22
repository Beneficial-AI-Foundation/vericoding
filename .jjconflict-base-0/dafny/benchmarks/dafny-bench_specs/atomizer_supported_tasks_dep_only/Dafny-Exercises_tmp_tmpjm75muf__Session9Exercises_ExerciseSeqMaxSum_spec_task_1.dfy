

// ATOM 


function Sum(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
{
    if (i==j) then 0
    else Sum(v,i,j-1)+v[j-1]
}


// ATOM 

predicate SumMaxToRight(v:array<int>,i:int,s:int)
reads v
requires 0<=i<v.Length
{
forall l,ss {:induction l}::0<=l<=i && ss==i+1==> Sum(v,l,ss)<=s
}


// SPEC 

method segMaxSum(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum(v,k,i+1) &&  SumMaxToRight(v,i,s)
{
}
 


// ATOM 


function Sum(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
{
    if (i==j) then 0
    else Sum(v,i,j-1)+v[j-1]
}
2

//Now do the same but with a loop from right to left
// ATOM 

predicate SumMaxToRight(v:array<int>,i:int,s:int)
reads v
requires 0<=i<v.Length
{
forall l,ss {:induction l}::0<=l<=i && ss==i+1==> Sum(v,l,ss)<=s
}
2

//ATOM_PLACEHOLDER_segSumaMaxima2

