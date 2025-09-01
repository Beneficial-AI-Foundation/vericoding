function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma MinSubArraySumLemma(a: seq<int>, s: int, t: int, minSoFar: int, startIndex: int) returns (minTotal: int, start: int, end: int)
  requires 0 <= s <= t <= |a|
  requires minSoFar <= Sum(a, s, t)
  ensures 0 <= start <= end <= |a|
  ensures minTotal == Sum(a, start, end)
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) >= minTotal
  decreases |a| - t
{
  if t == |a| {
    minTotal := minSoFar;
    start := s;
    end := t;
  } else {
    var currentSum : int := Sum(a, s, t);
    var newSum : int := currentSum + a[t];
    var newMin : int;
    if newSum < minSoFar {
      newMin := newSum;
    } else {
      newMin := minSoFar;
    }
    MinSubArraySumLemma(a, s, t+1, newMin, startIndex);
    minTotal := minSoFar;
    start := s;
    end := t;
  }
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
  } else {
    s := Sum(a, 0, 1);
    for i := 0 to |a|
      invariant forall p,q :: 0 <= p <= q <= i ==> Sum(a, p, q) >= s
      invariant exists k, m :: 0 <= k <= m <= i && s == Sum(a, k, m)
    {
      var currentSum := 0;
      for j := i to |a|
        invariant currentSum == Sum(a, i, j)
        invariant forall p,q :: 0 <= p <= i <= q <= j ==> Sum(a, p, q) >= s
      {
        currentSum := currentSum + a[j];
        if currentSum < s {
          s := currentSum;
        }
      }
    }
  }
}
// </vc-code>

