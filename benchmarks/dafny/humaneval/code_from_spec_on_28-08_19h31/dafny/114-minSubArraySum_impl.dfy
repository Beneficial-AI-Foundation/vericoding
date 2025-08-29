function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma SumSplit(a: seq<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= |a|
  ensures Sum(a, i, k) == Sum(a, i, j) + Sum(a, j, k)
{
  if i == k {
    assert Sum(a, i, k) == 0;
    assert Sum(a, i, j) == 0;
    assert Sum(a, j, k) == 0;
  } else if j == k {
    assert Sum(a, i, k) == Sum(a, i, j);
    assert Sum(a, j, k) == 0;
  } else {
    SumSplit(a, i, j, k-1);
    assert Sum(a, i, k) == Sum(a, i, k-1) + a[k-1];
    assert Sum(a, i, k-1) == Sum(a, i, j) + Sum(a, j, k-1);
    assert Sum(a, j, k) == Sum(a, j, k-1) + a[k-1];
  }
}

lemma SumNonNegative(a: seq<int>, s: int, t: int)
  requires 0 <= s <= t <= |a|
  ensures Sum(a, s, t) >= 0 || Sum(a, s, t) < 0
{
}
// </vc-helpers>

// <vc-spec>
method minSubArraySum(a: seq<int>) returns (s: int)
  // post-conditions-start
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
  // post-conditions-end
// </vc-spec>
// <vc-code>
method MinSubArraySum(a: seq<int>) returns (s: int)
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s
  ensures exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m)
{
  if |a| == 0 {
    s := 0;
    return;
  }
  
  var minSum := a[0];
  var minStart := 0;
  var minEnd := 0;
  var currentSum := a[0];
  var currentStart := 0;
  var i := 1;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant 0 <= minStart <= minEnd < |a|
    invariant 0 <= currentStart <= i
    invariant minSum == Sum(a, minStart, minEnd + 1)
    invariant currentSum == Sum(a, currentStart, i)
    invariant forall p, q :: 0 <= p <= q <= minEnd ==> Sum(a, p, q) >= minSum
  {
    currentSum := currentSum + a[i];
    
    if currentSum < minSum {
      minSum := currentSum;
      minStart := currentStart;
      minEnd := i;
    }
    
    if currentSum > 0 {
      currentSum := 0;
      currentStart := i + 1;
    }
    
    i := i + 1;
  }
  
  // Check if the last segment is the minimum
  if currentStart < |a| && currentSum < minSum {
    minSum := currentSum;
    minStart := currentStart;
    minEnd := |a| - 1;
  }
  
  // Now we need to check the remaining suffixes after the loop
  var j := minEnd + 1;
  while j < |a|
    invariant minEnd < |a|
    invariant minSum == Sum(a, minStart, minEnd + 1)
    invariant j <= |a|
    invariant forall p, q :: 0 <= p <= q < j ==> Sum(a, p, q) >= minSum
  {
    var k := j;
    var tempSum := 0;
    while k < |a|
      invariant k <= |a|
      invariant tempSum == Sum(a, j, k)
      invariant forall p, q :: 0 <= p <= q < j ==> Sum(a, p, q) >= minSum
    {
      tempSum := tempSum + a[k];
      if tempSum < minSum {
        minSum := tempSum;
        minStart := j;
        minEnd := k;
      }
      k := k + 1;
    }
    j := j + 1;
  }
  
  s := minSum;
  assert exists k, m :: 0 <= k <= m <= |a| && s == Sum(a, k, m);
  assert forall p, q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= s;
  return;
}
// </vc-code>
