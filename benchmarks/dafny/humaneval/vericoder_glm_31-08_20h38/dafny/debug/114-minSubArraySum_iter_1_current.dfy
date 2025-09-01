function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
lemma Sum_properties(a: seq<int>, s: int, t: int, u: int)
  requires 0 <= s <= t <= u <= |a|
  ensures Sum(a, s, u) == Sum(a, s, t) + Sum(a, t, u)
{
  if s == u {
    calc {
      Sum(a, s, u);
      0;
      0 + 0;
      Sum(a, s, t) + Sum(a, t, u);
    }
  } else if t == u {
    calc {
      Sum(a, s, u);
      Sum(a, s, u-1) + a[u-1];
      Sum(a, s, t) + Sum(a, t, u-1) + a[u-1];
      Sum(a, s, t) + (Sum(a, t, u-1) + a[u-1]);
      Sum(a, s, t) + Sum(a, t, u);
    }
  } else {
    calc {
      Sum(a, s, u);
      Sum(a, s, u-1) + a[u-1];
      Sum(a, s, t) + Sum(a, t, u-1) + a[u-1];
      { Sum_properties(a, s, t, u-1); }
      Sum(a, s, u);
      Sum(a, s, t) + (Sum(a, t, u-1) + a[u-1]);
      Sum(a, s, t) + Sum(a, t, u);
    }
  }
}

lemma Sum_non_empty(a: seq<int>, k: int, m: int)
  requires 0 <= k < m <= |a|
  ensures Sum(a, k, m) <= Sum(a, k, m-1) || Sum(a, k, m) <= Sum(a, k+1, m)
{
  var s1 := Sum(a, k, m-1);
  var s2 := Sum(a, k+1, m);
  calc {
    Sum(a, k, m);
    s1 + a[m-1];
    { Sum_properties(a, k, k+1, m); }
    a[k] + s2;
  }
  
  if a[k] <= a[m-1] {
    assert Sum(a, k, m) == s1 + a[m-1] >= s1;
  } else {
    assert Sum(a, k, m) == a[k] + s2 >= s2;
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
    return 0;
  }

  var min := Sum(a, 0, |a|);
  var n := |a|;
  
  ghost var k := 0;
  ghost var m := n;

  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall p,q :: 0 <= p <= q <= i ==> Sum(a, p, q) >= min
    invariant exists k, m :: 0 <= k <= m <= i && min == Sum(a, k, m)
  {
    var sum := 0;
    ghost var start := i;
    for j := i to n
      invariant i <= j <= n
      invariant sum == Sum(a, i, j)
      invariant sum >= min ==> (forall p,q :: i <= p <= q < j ==> Sum(a, p, q) >= min)
      invariant sum < min ==> min == Sum(a, start, j-1) && start <= j-1 < j
    {
      if j < n {
        sum := sum + a[j];
        if sum < min {
          min := sum;
          k := i;
          m := j + 1;
        }
      }
    }
  }
  
  return min;
}
// </vc-code>

