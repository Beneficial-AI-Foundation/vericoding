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


// IMPL segMaxSum

method segMaxSum(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum(v,k,i+1) &&  SumMaxToRight(v,i,s)
{
    s := v[i];
    k := i;
    var curr_sum := v[i];
    var j := i - 1;
    
    while j >= 0
        invariant -1 <= j <= i - 1
        invariant s == Sum(v, k, i+1)
        invariant 0 <= k <= i
        invariant curr_sum == Sum(v, j+1, i+1)
        /* code modified by LLM (iteration 1): Enhanced invariant to maintain postcondition property */
        invariant forall l :: j+1 <= l <= i ==> Sum(v, l, i+1) <= s
        invariant forall l :: 0 <= l <= j ==> Sum(v, l, i+1) <= s
    {
        curr_sum := curr_sum + v[j];
        if curr_sum > s {
            s := curr_sum;
            k := j;
        }
        j := j - 1;
    }
}


// ATOM 


function Sum2(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
{
    if (i==j) then 0
    else v[i]+Sum2(v,i+1,j)
}


//Now do the same but with a loop from right to left
// ATOM 

//Now do the same but with a loop from right to left
predicate SumMaxToRight2(v:array<int>,j:int,i:int,s:int)//maximum sum stuck to the right
reads v
requires 0<=j<=i<v.Length
{(forall l,ss {:induction l}::j<=l<=i && ss==i+1 ==> Sum2(v,l,ss)<=s)}


/* code modified by LLM (iteration 1): Added helper lemma to establish relationship between Sum2 segments */
lemma Sum2Extend(v: array<int>, start: int, end: int)
    requires 0 <= start < end <= v.Length
    ensures Sum2(v, start, end) == v[start] + Sum2(v, start+1, end)
{
    // This follows directly from the definition of Sum2
}

/* code modified by LLM (iteration 1): Added lemma to help with Sum2 reasoning */
lemma Sum2Properties(v: array<int>, i: int, j: int, k: int)
    requires 0 <= i <= j <= k <= v.Length
    ensures Sum2(v, i, k) == Sum2(v, i, j) + Sum2(v, j, k)
{
    if i == j {
        assert Sum2(v, i, j) == 0;
    } else {
        Sum2Properties(v, i+1, j, k);
        Sum2Extend(v, i, k);
        Sum2Extend(v, i, j);
    }
}

// IMPL segSumaMaxima2

method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
//Implement and verify
{
    s := v[i];
    k := i;
    var curr_sum := v[i];
    var j := i - 1;
    
    while j >= 0
        invariant -1 <= j <= i - 1
        invariant s == Sum2(v, k, i+1)
        invariant 0 <= k <= i
        invariant curr_sum == Sum2(v, j+1, i+1)
        /* code modified by LLM (iteration 1): Added invariants to maintain postcondition */
        invariant forall l :: j+1 <= l <= i ==> Sum2(v, l, i+1) <= s
        invariant forall l :: 0 <= l <= j ==> Sum2(v, l, i+1) <= s
    {
        /* code modified by LLM (iteration 1): Added assertion to help with Sum2 extension */
        assert Sum2(v, j, i+1) == v[j] + Sum2(v, j+1, i+1) by {
            Sum2Extend(v, j, i+1);
        }
        
        curr_sum := curr_sum + v[j];
        
        /* code modified by LLM (iteration 1): Added assertion to establish curr_sum equals Sum2(v,j,i+1) */
        assert curr_sum == Sum2(v, j, i+1);
        
        if curr_sum > s {
            s := curr_sum;
            k := j;
        }
        
        /* code modified by LLM (iteration 1): Added assertion to maintain invariant for all segments starting at j */
        assert forall l :: 0 <= l <= j ==> Sum2(v, l, i+1) <= s;
        
        j := j - 1;
    }
    
    /* code modified by LLM (iteration 1): Added final assertion to establish postcondition */
    assert forall l :: 0 <= l <= i ==> Sum2(v, l, i+1) <= s;
}