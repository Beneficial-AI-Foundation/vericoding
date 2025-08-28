predicate isPeek(v:array<int>,i:int)
 reads v
 requires 0<=i<v.Length
 {forall k::0<=k<i ==> v[i]>=v[k]}

 function peekSum(v:array<int>,i:int):int
 decreases i 
 reads v
 requires 0<=i<=v.Length
 {
  if (i==0) then 0
  else if isPeek(v,i-1) then v[i-1]+peekSum(v,i-1)
  else peekSum(v,i-1)
 }

// <vc-helpers>
lemma PeekSumCorrect(v: array<int>, i: int)
  requires 0 <= i <= v.Length
  ensures peekSum(v, i) == SumOfPeaks(v, i)
{
  if (i == 0) {
  } else {
    if (isPeek(v, i-1)) {
      calc {
        peekSum(v, i);
        v[i-1] + peekSum(v, i-1);
        { PeekSumCorrect(v, i-1); }
        v[i-1] + SumOfPeaks(v, i-1);
        SumOfPeaks(v, i);
      }
    } else {
      calc {
        peekSum(v, i);
        peekSum(v, i-1);
        { PeekSumCorrect(v, i-1); }
        SumOfPeaks(v, i-1);
        SumOfPeaks(v, i);
      }
    }
  }
}

function SumOfPeaks(v: array<int>, i: int): int
  requires 0 <= i <= v.Length
  reads v
  decreases i
{
  if i == 0 then 0
  else if isPeek(v, i-1) then v[i-1] + SumOfPeaks(v, i-1)
  else SumOfPeaks(v, i-1)
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mPeekSum(v:array<int>) returns (sum:int)
 requires  v.Length>0
 ensures sum==peekSum(v,v.Length)
 //Implement and verify an O(v.Length) algorithm to solve this problem
// </vc-spec>
// </vc-spec>

// <vc-code>
method ComputePeekSum(v: array<int>) returns (sum: int)
  requires v.Length > 0
  ensures sum == peekSum(v, v.Length)
{
  sum := 0;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant sum == peekSum(v, i)
  {
    if (isPeek(v, i)) {
      sum := sum + v[i];
    }
    i := i + 1;
  }
  assert sum == peekSum(v, v.Length);
}
// </vc-code>
