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
    /* code modified by LLM (iteration 1): Initialize with first sum and iterate through all positions */
    s := Sum2(v, 0, i+1);
    k := 0;
    
    var j := 1;
    while j <= i
        invariant 1 <= j <= i + 1
        invariant 0 <= k <= i
        invariant s == Sum2(v, k, i+1)
        invariant forall l :: 0 <= l < j ==> Sum2(v, l, i+1) <= s
        invariant forall l :: 0 <= l <= i ==> (l < j ==> Sum2(v, l, i+1) <= s)
    {
        var currentSum := Sum2(v, j, i+1);
        if currentSum > s {
            s := currentSum;
            k := j;
        }
        j := j + 1;
    }
    
    /* code modified by LLM (iteration 1): Strengthen loop invariant and add lemma call for complete coverage */
    assert j == i + 1;
    assert forall l :: 0 <= l <= i ==> Sum2(v, l, i+1) <= s;
    
    /* code modified by LLM (iteration 1): Helper lemma call to establish SumMaxToRight2 */
    SumMaxToRight2Helper(v, 0, i, s);
}

/* code modified by LLM (iteration 1): Helper lemma to prove SumMaxToRight2 property */
lemma SumMaxToRight2Helper(v: array<int>, j: int, i: int, s: int)
    reads v
    requires 0 <= j <= i < v.Length
    requires forall l :: j <= l <= i ==> Sum2(v, l, i+1) <= s
    ensures SumMaxToRight2(v, j, i, s)
{
    // The proof follows directly from the precondition
    // since SumMaxToRight2 is defined as exactly this property
}