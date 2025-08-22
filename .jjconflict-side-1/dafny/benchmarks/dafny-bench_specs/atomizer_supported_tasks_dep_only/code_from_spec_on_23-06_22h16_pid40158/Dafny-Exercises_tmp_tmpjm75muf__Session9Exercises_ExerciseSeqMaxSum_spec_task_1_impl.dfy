//ATOM 
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
ensures 0<=k<=i && s==Sum(v,k,i+1) &&  SumMaxToRight(v,i,s)
{
    s := v[i];
    k := i;
    var j := i - 1;
    
    while j >= 0
    invariant -1 <= j <= i - 1
    invariant 0 <= k <= i
    invariant s == Sum(v,k,i+1)
    /* code modified by LLM (iteration 2): Strengthened invariant to ensure s is maximum among all segments from positions > j to i+1 */
    invariant forall l :: j < l <= i ==> Sum(v,l,i+1) <= s
    /* code modified by LLM (iteration 2): Added invariant to track that s is achievable from some position > j */
    invariant exists l :: j < l <= i && Sum(v,l,i+1) == s
    {
        /* code modified by LLM (iteration 2): Calculate sum from current position j to i+1 */
        var sumFromJ := Sum(v,j,i+1);
        
        if sumFromJ > s {
            s := sumFromJ;
            k := j;
        }
        j := j - 1;
    }
    
    /* code modified by LLM (iteration 2): Final assertion to establish SumMaxToRight postcondition */
    assert forall l :: 0 <= l <= i ==> Sum(v,l,i+1) <= s;
}