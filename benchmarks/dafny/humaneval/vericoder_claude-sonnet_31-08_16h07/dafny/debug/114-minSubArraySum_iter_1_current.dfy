function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma SumMonotonic(a: seq<int>, s: int, t: int, u: int)
  requires 0 <= s <= t <= u <= |a|
  ensures Sum(a, s, t) + Sum(a, t, u) == Sum(a, s, u)
{
  if t == u {
    assert Sum(a, t, u) == 0;
    assert Sum(a, s, t) + Sum(a, t, u) == Sum(a, s, t) == Sum(a, s, u);
  } else {
    SumMonotonic(a, s, t, u-1);
    assert Sum(a, s, t) + Sum(a, t, u-1) == Sum(a, s, u-1);
    assert Sum(a, t, u) == Sum(a, t, u-1) + a[u-1];
    assert Sum(a, s, u) == Sum(a, s, u-1) + a[u-1];
  }
}

lemma SumEmpty(a: seq<int>, s: int)
  requires 0 <= s <= |a|
  ensures Sum(a, s, s) == 0
{
}

lemma SumExtend(a: seq<int>, s: int, t: int)
  requires 0 <= s <= t < |a|
  ensures Sum(a, s, t+1) == Sum(a, s, t) + a[t]
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
{
  if |a| == 0 {
    s := 0;
    return;
  }
  
  s := 0;
  var minStart := 0;
  var minEnd := 0;
  
  var i := 0;
  while i <= |a|
    invariant 0 <= i <= |a|
    invariant 0 <= minStart <= minEnd <= |a|
    invariant s == Sum(a, minStart, minEnd)
    invariant forall p, q :: 0 <= p <= q <= i ==> Sum(a, p, q) >= s
  {
    var j := i;
    var currentSum := 0;
    
    while j <= |a|
      invariant i <= j <= |a|
      invariant currentSum == Sum(a, i, j)
      invariant forall q :: i <= q <= j ==> Sum(a, i, q) >= s
    {
      if currentSum < s {
        s := currentSum;
        minStart := i;
        minEnd := j;
      }
      
      if j == |a| {
        break;
      }
      
      currentSum := currentSum + a[j];
      j := j + 1;
    }
    
    i := i + 1;
  }
}
// </vc-code>

