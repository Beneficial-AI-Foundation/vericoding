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
lemma Sum2EquivalentToSum(v: array<int>, i: int, j: int)
  requires 0 <= i <= j <= v.Length
  ensures Sum2(v, i, j) == Sum(v, i, j)
  decreases j - i
{
  if i == j {
    assert Sum2(v, i, j) == 0 == Sum(v, i, j);
  } else {
    Sum2EquivalentToSum(v, i + 1, j);
    assert Sum2(v, i, j) == v[i] + Sum2(v, i + 1, j);
    assert Sum(v, i, j) == Sum(v, i, j - 1) + v[j - 1];
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
//Implement and verify
// </vc-spec>
// </vc-spec>

// <vc-code>
method segSumaMaxima2Impl(v: array<int>, i: int) returns (s: int, k: int)
  requires v.Length > 0 && 0 <= i < v.Length
  ensures 0 <= k <= i && s == Sum2(v, k, i + 1) && SumMaxToRight2(v, 0, i, s)
{
  s := v[i];
  k := i;
  var currentSum := v[i];
  var l := i;
  
  while l > 0
    invariant 0 <= l <= i
    invariant currentSum == Sum2(v, l, i + 1)
    invariant 0 <= k <= i
    invariant s == Sum2(v, k, i + 1)
    invariant forall m :: l <= m <= i ==> Sum2(v, m, i + 1) <= s
    decreases l
  {
    l := l - 1;
    currentSum := currentSum + v[l];
    if currentSum > s {
      s := currentSum;
      k := l;
    }
  }
  
  // Postcondition for SumMaxToRight2
  assert forall m :: 0 <= m <= i ==> Sum2(v, m, i + 1) <= s;
}
// </vc-code>
