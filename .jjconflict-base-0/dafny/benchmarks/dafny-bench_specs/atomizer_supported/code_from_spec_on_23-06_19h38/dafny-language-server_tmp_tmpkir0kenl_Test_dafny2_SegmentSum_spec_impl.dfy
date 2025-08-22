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
  k := 0;
  m := 0;
  
  if |a| == 0 {
    return;
  }
  
  var maxSum := 0;
  var i := 0;
  
  while i < |a|
    /* code modified by LLM (iteration 1): strengthened outer loop invariant to properly track maximum over all subarrays */
    invariant 0 <= i <= |a|
    invariant 0 <= k <= m <= |a|
    invariant forall p,q :: 0 <= p < i && p <= q <= |a| ==> Sum(a, p, q) <= maxSum
    invariant Sum(a, k, m) == maxSum
  {
    var j := i;
    var currentSum := 0;
    
    while j < |a|
      /* code modified by LLM (iteration 1): enhanced inner loop invariants to maintain correctness */
      invariant i <= j <= |a|
      invariant currentSum == Sum(a, i, j)
      invariant 0 <= k <= m <= |a|
      invariant forall p,q :: 0 <= p < i && p <= q <= |a| ==> Sum(a, p, q) <= maxSum
      invariant forall q :: i <= q <= j ==> Sum(a, i, q) <= maxSum
      invariant Sum(a, k, m) == maxSum
    {
      currentSum := currentSum + a[j];
      
      if currentSum > maxSum {
        k := i;
        m := j + 1;
        maxSum := currentSum;
      }
      
      j := j + 1;
    }
    
    i := i + 1;
  }
}