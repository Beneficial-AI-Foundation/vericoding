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
lemma Sum2_decomp(v:array<int>, a:int, b:int)
  requires 0 <= a < b <= v.Length
  ensures Sum2(v,a,b) == v[a] + Sum2(v,a+1,b)
{
}
// </vc-helpers>

// <vc-spec>
method segSumaMaxima2(v:array<int>,i:int) returns (s:int,k:int)
requires v.Length>0 && 0<=i<v.Length
ensures 0<=k<=i && s==Sum2(v,k,i+1) &&  SumMaxToRight2(v,0,i,s)
//Implement and verify
// </vc-spec>
// <vc-code>
{
  var j := i;
  var cur := Sum2(v,i,i+1);
  var best := i;
  var bestval := cur;
  while j > 0
    invariant 0 <= j <= i
    invariant cur == Sum2(v,j,i+1)
    invariant 0 <= best <= i
    invariant bestval == Sum2(v,best,i+1)
    invariant forall l {:trigger Sum2(v,l,i+1)} :: j <= l <= i ==> Sum2(v,l,i+1) <= bestval
  {
    var jm := j - 1;
    var newcur := cur + v[jm];
    assert 0 <= jm < i+1 && i+1 <= v.Length;
    assert Sum2(v,jm+1,i+1) == cur;
    Sum2_decomp(v,jm,i+1);
    assert Sum2(v,jm,i+1) == v[jm] + Sum2(v,jm+1,i+1);
    assert Sum2(v,jm,i+1) == newcur;
    j := jm;
    cur := newcur;
    if cur >= bestval {
      best := j;
      bestval := cur;
    }
  }
  s := bestval;
  k := best;
}
// </vc-code>

