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
lemma Sum2Unfold(v:array<int>, i:int, j:int)
  requires 0 <= i < j <= v.Length
  ensures Sum2(v,i,j) == v[i] + Sum2(v,i+1,j)
{}
// </vc-helpers>

// <vc-spec>
method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
//Implement and verify
// </vc-spec>
// <vc-code>
{
  var l := i;
  var cur := 0;
  var sMax := v[i];
  var kBest := i;
  while l >= 0
    invariant -1 <= l <= i
    invariant cur == Sum2(v, l+1, i+1)
    invariant 0 <= kBest <= i
    invariant sMax == Sum2(v, kBest, i+1)
    invariant forall t {:trigger Sum2(v, t, i+1)} | l+1 <= t <= i :: Sum2(v, t, i+1) <= sMax
    decreases l + 1
  {
    assert 0 <= l < i+1 <= v.Length;
    Sum2Unfold(v, l, i+1);
    cur := v[l] + cur;
    assert cur == Sum2(v, l, i+1);

    if cur >= sMax {
      sMax := cur;
      kBest := l;
    }
    assert Sum2(v, l, i+1) <= sMax;

    l := l - 1;
    assert cur == Sum2(v, l+1, i+1);
  }

  s := sMax;
  k := kBest;
  assert 0 <= k <= i;
  assert s == Sum2(v, k, i+1);
  assert (forall l0, ss {:trigger Sum2(v, l0, ss)} | 0 <= l0 <= i && ss == i+1 :: Sum2(v, l0, ss) <= s);
  assert SumMaxToRight2(v, 0, i, s);
}
// </vc-code>

