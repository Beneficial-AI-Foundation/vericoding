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
lemma Sum2Property(v:array<int>, i:int, j:int)
requires 0<=i<=j<=v.Length
ensures Sum2(v,i,j) == Sum2(v,i,i) + Sum2(v,i,j)
{
}

lemma Sum2Extended(v:array<int>, i:int, j:int)
requires 0<=i<j<=v.Length
ensures Sum2(v,i,j) == v[i] + Sum2(v,i+1,j)
{
}

lemma SumMaxToRight2Property(v:array<int>, j:int, i:int, s:int, newS:int, newK:int)
requires 0<=j<=i<v.Length
requires j+1 <= i ==> SumMaxToRight2(v,j+1,i,s)
requires 0<=newK<=i<v.Length
requires newS == Sum2(v,newK,i+1)
requires j<=newK<=i
requires newS >= s
requires newS >= Sum2(v,j,i+1)
ensures SumMaxToRight2(v,j,i,newS)
{
}

lemma EstablishSumMaxToRight2Base(v:array<int>, i:int, s:int)
requires 0<=i<v.Length
requires s == Sum2(v,i,i+1)
ensures SumMaxToRight2(v,i,i,s)
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
  s := v[i];
  k := i;
  
  var j := i - 1;
  
  while j >= 0
  invariant -1 <= j <= i - 1
  invariant 0 <= k <= i
  invariant s == Sum2(v, k, i + 1)
  invariant j == i - 1 ==> SumMaxToRight2(v, i, i, s)
  invariant j < i - 1 ==> SumMaxToRight2(v, j + 1, i, s)
  decreases j + 1
  {
    var currentSum := Sum2(v, j, i + 1);
    
    if currentSum > s {
      s := currentSum;
      k := j;
    }
    
    j := j - 1;
  }
}
// </vc-code>

