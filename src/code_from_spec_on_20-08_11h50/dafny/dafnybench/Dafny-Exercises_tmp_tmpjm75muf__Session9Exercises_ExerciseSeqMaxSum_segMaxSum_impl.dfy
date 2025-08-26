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

// <vc-helpers>
lemma SumProperty(v:array<int>, i:int, j:int, k:int)
requires 0<=i<=j<=k<=v.Length
ensures Sum(v,i,k) == Sum(v,i,j) + Sum(v,j,k)
decreases k
{
    if j == k {
        // Base case: Sum(v,j,k) == 0
    } else {
        // Inductive case
        SumProperty(v, i, j, k-1);
    }
}

lemma SumExtendLeft(v:array<int>, i:int, j:int)
requires 0 < i <= j <= v.Length
ensures Sum(v, i-1, j) == v[i-1] + Sum(v, i, j)
decreases j
{
    if i == j {
        // Base case
    } else {
        // Inductive case
        SumExtendLeft(v, i, j-1);
    }
}
// </vc-helpers>

method segMaxSum(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum(v,k,i+1) &&  SumMaxToRight(v,i,s)
// </vc-spec>
// <vc-code>
{
  s := v[i];
  k := i;
  var current_sum := v[i];
  var l := i;
  
  while l > 0
    invariant 0 <= l <= i
    invariant current_sum == Sum(v, l, i+1)
    invariant 0 <= k <= i
    invariant s == Sum(v, k, i+1)
    invariant forall m {:trigger Sum(v, m, i+1)} :: l <= m <= i ==> Sum(v, m, i+1) <= s
  {
    l := l - 1;
    SumExtendLeft(v, l+1, i+1);
    current_sum := current_sum + v[l];
    
    if current_sum > s {
      s := current_sum;
      k := l;
    }
  }
}
// </vc-code>

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