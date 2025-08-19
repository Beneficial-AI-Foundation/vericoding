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


//IMPL segMaxSum

method segMaxSum(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum(v,k,i+1) && SumMaxToRight(v,i,s)
{
    s := v[i];
    k := i;
    
    var currentSum := v[i];
    var j := i;
    
    while j > 0
        invariant 0 <= j <= i
        invariant currentSum == Sum(v, j, i+1)
        invariant s >= currentSum
        invariant 0 <= k <= i && s == Sum(v, k, i+1)
        /* code modified by LLM (iteration 2): Added trigger for quantifier to fix warning */
        invariant forall l {:trigger Sum(v, l, i+1)} :: j <= l <= i ==> Sum(v, l, i+1) <= s
    {
        j := j - 1;
        /* code modified by LLM (iteration 2): Added lemma call to establish sum decomposition property */
        SumDecompositionLemma(v, j, j+1, i+1);
        currentSum := currentSum + v[j];
        
        if currentSum > s {
            s := currentSum;
            k := j;
        }
    }
    
    /* code modified by LLM (iteration 2): Added trigger for quantifier to fix warning */
    assert forall l {:trigger Sum(v, l, i+1)} :: 0 <= l <= i ==> Sum(v, l, i+1) <= s;
}

/* code modified by LLM (iteration 2): Removed reads clause from lemma - lemmas cannot have reads clauses */
lemma SumDecompositionLemma(v: array<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.Length
    ensures Sum(v, i, k) == Sum(v, i, j) + Sum(v, j, k)
{
    if i == j {
        assert Sum(v, i, j) == 0;
        assert Sum(v, i, k) == Sum(v, j, k);
    } else {
        SumDecompositionLemma(v, i, j-1, k);
        assert Sum(v, i, k) == Sum(v, i, j-1) + Sum(v, j-1, k);
        assert Sum(v, j-1, k) == Sum(v, j-1, j) + Sum(v, j, k);
        assert Sum(v, j-1, j) == v[j-1];
        assert Sum(v, i, j) == Sum(v, i, j-1) + v[j-1];
    }
}