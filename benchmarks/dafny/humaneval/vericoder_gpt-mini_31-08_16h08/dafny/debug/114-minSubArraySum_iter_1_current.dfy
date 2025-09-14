function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
// No helper definitions required for this proof.
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
  var n := |a|;
  var min := 0;
  var k := 0;
  var m := 0;

  if n > 0 {
    // Process start index i = 0
    var i := 0;
    var j := i;
    var sum := 0;
    while j < n
      decreases n - j
      invariant i == 0
      invariant i <= j <= n
      invariant sum == Sum(a, i, j)
      invariant forall p,q :: 0 <= p <= q <= n && (p < i || (p == i && q <= j)) ==> Sum(a,p,q) >= min
      invariant exists p,q :: 0 <= p <= q <= n && (p < i || (p == i && q <= j)) && min == Sum(a,p,q)
    {
      sum := sum + a[j];
      j := j + 1;
      if sum < min {
        min := sum;
        k := i;
        m := j;
      }
    }

    // Process remaining start indices i = 1 .. n-1
    var ii := 1;
    while ii < n
      decreases n - ii
      invariant 0 <= ii <= n
      invariant forall p,q :: 0 <= p <= q <= n && p < ii ==> Sum(a,p,q) >= min
      invariant exists p,q :: 0 <= p <= q <= n && p < ii && min == Sum(a,p,q)
    {
      i := ii;
      j := i;
      sum := 0;
      while j < n
        decreases n - j
        invariant i <= j <= n
        invariant sum == Sum(a, i, j)
        invariant forall p,q :: 0 <= p <= q <= n && (p < i || (p == i && q <= j)) ==> Sum(a,p,q) >= min
        invariant exists p,q :: 0 <= p <= q <= n && (p < i || (p == i && q <= j)) && min == Sum(a,p,q)
      {
        sum := sum + a[j];
        j := j + 1;
        if sum < min {
          min := sum;
          k := i;
          m := j;
        }
      }
      ii := ii + 1;
    }
  }

  s := min;
}
// </vc-code>

