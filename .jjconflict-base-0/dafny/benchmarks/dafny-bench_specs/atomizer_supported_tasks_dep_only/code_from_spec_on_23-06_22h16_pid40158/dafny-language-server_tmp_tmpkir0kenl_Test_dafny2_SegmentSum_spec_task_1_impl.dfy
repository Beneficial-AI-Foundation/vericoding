// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

//ATOM 
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

//IMPL 
method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{
  if |a| == 0 {
    k, m := 0, 0;
    return;
  }
  
  k, m := 0, 0;
  var maxSum := 0;
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= k <= m <= |a|
    invariant maxSum == Sum(a, k, m)
    /* code modified by LLM (iteration 1): strengthened outer loop invariant to ensure all segments with start positions < i are covered */
    invariant forall p,q :: 0 <= p < i && p <= q <= |a| ==> Sum(a, p, q) <= maxSum
  {
    var j := i;
    var currentSum := 0;
    while j < |a|
      invariant i <= j <= |a|
      invariant currentSum == Sum(a, i, j)
      invariant 0 <= k <= m <= |a|
      invariant maxSum == Sum(a, k, m)
      /* code modified by LLM (iteration 1): strengthened inner loop invariant to cover all segments with start < i */
      invariant forall p,q :: 0 <= p < i && p <= q <= |a| ==> Sum(a, p, q) <= maxSum
      /* code modified by LLM (iteration 1): added invariant to cover segments starting at current position i */
      invariant forall q :: i <= q <= j ==> Sum(a, i, q) <= maxSum
    {
      currentSum := currentSum + a[j];
      j := j + 1;
      
      if currentSum > maxSum {
        k, m := i, j;
        maxSum := currentSum;
      }
    }
    i := i + 1;
  }
}