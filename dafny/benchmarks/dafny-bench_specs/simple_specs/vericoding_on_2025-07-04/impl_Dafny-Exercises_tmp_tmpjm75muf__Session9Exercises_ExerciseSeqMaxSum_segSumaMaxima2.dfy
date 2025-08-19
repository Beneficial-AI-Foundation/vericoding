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


//IMPL 

method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) && SumMaxToRight2(v,0,i,s)
//Implement and verify
{
    /* code modified by LLM (iteration 1): initialize with first position */
    s := Sum2(v, 0, i+1);
    k := 0;
    
    var j := 1;
    while j <= i
        invariant 1 <= j <= i+1
        invariant 0 <= k <= i
        invariant s == Sum2(v, k, i+1)
        /* code modified by LLM (iteration 1): invariant ensuring s is maximum over examined positions */
        invariant forall l :: 0 <= l < j ==> Sum2(v, l, i+1) <= s
        /* code modified by LLM (iteration 1): invariant ensuring k is in examined range */
        invariant 0 <= k < j
    {
        var currentSum := Sum2(v, j, i+1);
        if currentSum > s {
            s := currentSum;
            k := j;
        }
        j := j + 1;
    }
    
    /* code modified by LLM (iteration 1): assertion to establish postcondition */
    assert forall l :: 0 <= l <= i ==> Sum2(v, l, i+1) <= s;
    /* code modified by LLM (iteration 1): assertion to help prove SumMaxToRight2 */
    assert forall l, ss :: 0 <= l <= i && ss == i+1 ==> Sum2(v, l, ss) <= s;
}