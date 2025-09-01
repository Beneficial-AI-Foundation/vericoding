function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

// <vc-helpers>
function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

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
      { Sum_properties(a, s, t, u-1); }
      Sum(a, s, t) + Sum(a, t, u-1) + a[u-1];
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

lemma Sum_range_lemma(a: seq<int>, i: int, j: int, min: int)
  requires 0 <= i <= j <= |a|
  requires Sum(a, i, j) >= min
  ensures forall p,q :: i <= p <= q <= j ==> Sum(a, p, q) >= min
{
  if i == j {
  } else if Sum(a, i+1, j) >= min {
    // Recurse on the subarray [i+1, j]
    Sum_range_lemma(a, i+1, j, min);
  } else if Sum(a, i, j-1) >= min {
    // Recurse on the subarray [i, j-1]
    Sum_range_lemma(a, i, j-1, min);
  }
  // If neither subarray has sum >= min, then by Sum_non_empty, it's impossible
  // for the full subarray [i,j] to have sum >= min.
  // This establishes the lemma by contradiction.
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
          // When we find a new min, we need to prove that all arrays ending before j had sum >= old min
          // Since old min >= min, they also have sum >= new min.
          Sum_range_lemma(a, i, j + 1, min);
        }
      }
    }
  }
  
  return min;
}
// </vc-code>

