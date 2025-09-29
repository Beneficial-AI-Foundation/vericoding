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
lemma SumEquivalence(v:array<int>, i:int, j:int)
requires 0<=i<=j<=v.Length
ensures Sum(v,i,j) == Sum2(v,i,j)
decreases j-i
{
    if i == j {
        // Base case: both sums are 0
    } else {
        // Inductive case
        SumEquivalence(v, i+1, j);
        // Sum(v,i,j) = v[i] + Sum(v,i+1,j) = v[i] + Sum2(v,i+1,j) = Sum2(v,i,j)
    }
}

lemma SumSingleElement(v:array<int>, i:int)
requires 0<=i<v.Length
ensures Sum(v,i,i+1) == v[i]
{
    // Sum(v,i,i+1) = Sum(v,i,i) + v[i] = 0 + v[i] = v[i]
}

lemma SumExtendLeft(v:array<int>, i:int, j:int)
requires 0<=i<j<=v.Length
ensures Sum(v,i,j) == v[i] + Sum(v,i+1,j)
{
    if i+1 == j {
        SumSingleElement(v, i);
    } else {
        calc {
            Sum(v,i,j);
            Sum(v,i,j-1) + v[j-1];
            { SumExtendLeft(v, i, j-1); }
            v[i] + Sum(v,i+1,j-1) + v[j-1];
            v[i] + (Sum(v,i+1,j-1) + v[j-1]);
            v[i] + Sum(v,i+1,j);
        }
    }
}

lemma SumMonotonic(v:array<int>, i1:int, i2:int, j:int, maxSum:int)
requires 0<=i1<=i2<j<=v.Length
requires Sum(v,i2,j) <= maxSum
requires forall l::i1<=l<=i2-1 ==> v[l] >= 0
ensures Sum(v,i1,j) <= maxSum ==> true
decreases i2-i1
{
    if i1 == i2 {
        // Base case
    } else {
        SumExtendLeft(v, i1, j);
        SumMonotonic(v, i1+1, i2, j, maxSum);
    }
}
// </vc-helpers>

// <vc-spec>
method segMaxSum(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum(v,k,i+1) &&  SumMaxToRight(v,i,s)
// </vc-spec>
// <vc-code>
{
    s := v[i];
    k := i;
    var l := i;
    
    while l > 0
    invariant 0 <= l <= i
    invariant l <= k <= i
    invariant s == Sum(v,k,i+1)
    invariant forall m {:trigger Sum(v,m,i+1)} :: l <= m <= i ==> Sum(v,m,i+1) <= s
    decreases l
    {
        l := l - 1;
        var tempSum := Sum(v,l,i+1);
        
        assert tempSum == v[l] + Sum(v,l+1,i+1) by {
            SumExtendLeft(v, l, i+1);
        }
        
        if tempSum > s {
            s := tempSum;
            k := l;
        }
    }
}
// </vc-code>

