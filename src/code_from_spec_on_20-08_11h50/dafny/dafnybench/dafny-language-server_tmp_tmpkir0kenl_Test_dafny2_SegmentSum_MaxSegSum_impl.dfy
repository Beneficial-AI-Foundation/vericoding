lemma SumMonotonic(a: seq<int>, s: int, t1: int, t2: int)
  requires 0 <= s <= t1 <= t2 <= |a|
  requires forall i :: t1 <= i < t2 ==> a[i] >= 0
  ensures Sum(a, s, t1) <= Sum(a, s, t2)
{
  if t1 == t2 {
  } else {
    SumMonotonic(a, s, t1, t2-1);
  }
}

lemma SumEmpty(a: seq<int>, s: int)
  requires 0 <= s <= |a|
  ensures Sum(a, s, s) == 0
{
}

// <vc-helpers>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

lemma SumProperty(a: seq<int>, s: int, t: int)
  requires 0 <= s <= t <= |a|
  ensures Sum(a, s, t) == if s == t then 0 else Sum(a, s, t-1) + a[t-1]
{
}
// </vc-helpers>

// <vc-spec>
method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p, q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
// </vc-spec>

// <vc-code>
{
  k, m := 0, 0;
  var maxSum := Sum(a, 0, 0);
  
  var i := 0;
  while i <= |a|
    invariant 0 <= i <= |a| + 1
    invariant 0 <= k <= m <= |a|
    invariant maxSum == Sum(a, k, m)
    invariant forall p, q :: 0 <= p <= q <= |a| && p < i ==> Sum(a, p, q) <= maxSum
  {
    var j := i;
    while j <= |a|
      invariant i <= j <= |a| + 1
      invariant 0 <= k <= m <= |a|
      invariant maxSum == Sum(a, k, m)
      invariant forall p, q :: 0 <= p <= q <= |a| && p < i ==> Sum(a, p, q) <= maxSum
      invariant forall q :: i <= q <= |a| && q < j ==> Sum(a, i, q) <= maxSum
    {
      if i <= |a| && j <= |a| {
        var currentSum := Sum(a, i, j);
        if currentSum > maxSum {
          k, m := i, j;
          maxSum := currentSum;
        }
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>