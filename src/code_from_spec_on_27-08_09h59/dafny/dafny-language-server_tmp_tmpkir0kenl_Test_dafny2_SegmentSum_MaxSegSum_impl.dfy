// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma SumProperty(a: seq<int>, s: int, t: int, u: int)
  requires 0 <= s <= t <= u <= |a|
  ensures Sum(a, s, u) == Sum(a, s, t) + Sum(a, t, u)
{
  if t == u {
    assert Sum(a, t, u) == 0;
    assert Sum(a, s, u) == Sum(a, s, t);
  } else {
    SumProperty(a, s, t, u-1);
    assert Sum(a, s, u) == Sum(a, s, u-1) + a[u-1];
    assert Sum(a, s, u-1) == Sum(a, s, t) + Sum(a, t, u-1);
    assert Sum(a, t, u) == Sum(a, t, u-1) + a[u-1];
  }
}

lemma SumEmpty(a: seq<int>, s: int)
  requires 0 <= s <= |a|
  ensures Sum(a, s, s) == 0
{
}

lemma SumSingle(a: seq<int>, s: int)
  requires 0 <= s < |a|
  ensures Sum(a, s, s+1) == a[s]
{
}

lemma SumExtend(a: seq<int>, s: int, t: int)
  requires 0 <= s <= t < |a|
  ensures Sum(a, s, t+1) == Sum(a, s, t) + a[t]
{
}

lemma MaxSumPreservation(a: seq<int>, i: int, maxSum: int)
  requires 0 <= i < |a|
  requires forall p,q :: 0 <= p <= q <= i && q <= |a| ==> Sum(a, p, q) <= maxSum
  requires forall q :: i < q <= |a| ==> Sum(a, i, q) <= maxSum
  ensures forall p,q :: 0 <= p <= q <= i+1 && q <= |a| ==> Sum(a, p, q) <= maxSum
{
  forall p, q | 0 <= p <= q <= i+1 && q <= |a|
    ensures Sum(a, p, q) <= maxSum
  {
    if p <= i {
      assert Sum(a, p, q) <= maxSum;
    } else {
      assert p == i+1;
      assert q == i+1;
      assert Sum(a, p, q) == 0 <= maxSum;
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if |a| == 0 {
    return 0, 0;
  }
  
  k, m := 0, 0;
  var maxSum := 0;
  
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= k <= m <= |a|
    invariant forall p,q :: 0 <= p <= q <= i && q <= |a| ==> Sum(a, p, q) <= maxSum
    invariant maxSum == Sum(a, k, m)
  {
    var j := i;
    while j <= |a|
      invariant i <= j <= |a| + 1
      invariant 0 <= k <= m <= |a|
      invariant forall p,q :: 0 <= p <= q <= i && q <= |a| ==> Sum(a, p, q) <= maxSum
      invariant forall q :: i <= q <= j && q <= |a| ==> Sum(a, i, q) <= maxSum
      invariant maxSum == Sum(a, k, m)
    {
      if j == |a| { break; }
      
      var currentSum := Sum(a, i, j+1);
      if currentSum > maxSum {
        k, m := i, j+1;
        maxSum := currentSum;
      }
      
      j := j + 1;
    }
    
    assert forall q :: i <= q <= |a| ==> Sum(a, i, q) <= maxSum;
    
    if i < |a| {
      MaxSumPreservation(a, i, maxSum);
    }
    
    i := i + 1;
  }
  
  assert i == |a|;
  assert forall p,q :: 0 <= p <= q <= |a| && q <= |a| ==> Sum(a, p, q) <= maxSum;
}
// </vc-code>
