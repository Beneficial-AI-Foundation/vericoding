// <vc-spec>
function Sum(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
decreases j
{
    if (i==j) then 0
    else Sum(v,i,j-1)+v[j-1]
}

predicate SumMaxToRight(v:array<int>,i:int,s:int)
reads v
requires 0<=i<v.Length
{
forall l,ss {:induction l}::0<=l<=i && ss==i+1==> Sum(v,l,ss)<=s
}



function Sum2(v:array<int>,i:int,j:int):int
reads v
requires 0<=i<=j<=v.Length
decreases j-i
{
    if (i==j) then 0
    else v[i]+Sum2(v,i+1,j)
}

//Now do the same but with a loop from right to left
predicate SumMaxToRight2(v:array<int>,j:int,i:int,s:int)//maximum sum stuck to the right
reads v
requires 0<=j<=i<v.Length
{(forall l,ss {:induction l}::j<=l<=i && ss==i+1 ==> Sum2(v,l,ss)<=s)}

// <vc-helpers>
lemma Sum2Extend(v:array<int>, i:int, j:int, k:int)
requires 0 <= i <= j <= k <= v.Length
ensures Sum2(v, i, k) == Sum2(v, i, j) + Sum2(v, j, k)
decreases k - i
{
    if i == j {
        assert Sum2(v, i, j) == 0;
        assert Sum2(v, i, k) == Sum2(v, j, k);
    } else {
        Sum2Extend(v, i+1, j, k);
    }
}
// </vc-helpers>

method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
//Implement and verify
// </vc-spec>
// <vc-code>
{
    s := v[i];
    k := i;
    var currentSum := v[i];
    var j := i;
    
    while j > 0
    invariant 0 <= j <= i
    invariant 0 <= k <= i
    invariant s == Sum2(v, k, i+1)
    invariant currentSum == Sum2(v, j, i+1)
    invariant SumMaxToRight2(v, j, i, s)
    decreases j
    {
        j := j - 1;
        currentSum := currentSum + v[j];
        
        if currentSum > s {
            s := currentSum;
            k := j;
        }
    }
}
// </vc-code>