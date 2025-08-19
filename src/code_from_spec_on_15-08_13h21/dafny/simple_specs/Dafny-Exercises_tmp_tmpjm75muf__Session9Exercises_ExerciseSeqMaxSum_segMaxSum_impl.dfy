function Sum(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
{
  if (i==j) then 0
  else Sum(v,i,j-1)+v[j-1]
}

//ATOM

predicate SumMaxToRight(v:array<int>,i:int,s:int)
reads v
requires 0<=i<v.Length
{
forall l,ss {:induction l}::0<=l<=i && ss==i+1==> Sum(v,l,ss)<=s
}

//IMPL 

method segMaxSum(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum(v,k,i+1) && SumMaxToRight(v,i,s)
{
    s := Sum(v, 0, i+1);
    k := 0;
    
    var j := 1;
    while j <= i
        invariant 1 <= j <= i+1
        invariant 0 <= k <= i
        invariant s == Sum(v, k, i+1)
        /* code modified by LLM (iteration 1): added explicit trigger {:trigger Sum(v, l, i+1)} to quantifier to eliminate warning */
        invariant forall l {:trigger Sum(v, l, i+1)} :: 0 <= l < j ==> Sum(v, l, i+1) <= s
    {
        var currentSum := Sum(v, j, i+1);
        if currentSum > s {
            s := currentSum;
            k := j;
        }
        j := j + 1;
    }
}