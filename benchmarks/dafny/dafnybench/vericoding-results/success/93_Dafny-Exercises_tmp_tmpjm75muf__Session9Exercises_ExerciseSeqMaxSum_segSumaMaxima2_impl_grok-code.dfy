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
// No changes needed in helpers
// </vc-helpers>

// <vc-spec>
method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
//Implement and verify
// </vc-spec>
// <vc-code>
{
  s := v[i];
  k := i;
  var current_sum := v[i];
  var l := i - 1;
  while l >= 0
    invariant -1 <= l <= i
    invariant 0 <= k <= i
    invariant current_sum == Sum2(v, l+1, i+1)
    invariant forall m {:trigger Sum2(v,m,i+1)} :: 0 <= m <= i && m > l ==> Sum2(v, m, i+1) <= s
    invariant s == Sum2(v, k, i+1)
    decreases l
  {
    current_sum := current_sum + v[l];
    if current_sum > s {
      s := current_sum;
      k := l;
    }
    l := l - 1;
  }
}
// </vc-code>

