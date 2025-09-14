function comb2(n: int): int
  requires n >= 0
{
  n * (n - 1) / 2
}

predicate ValidInput(n: int, m: int)
{
  1 <= m <= n
}

function MinFriendshipPairs(n: int, m: int): int
  requires ValidInput(n, m)
{
  var k := n / m;
  var p := n % m;
  p * comb2(k + 1) + (m - p) * comb2(k)
}

function MaxFriendshipPairs(n: int, m: int): int
  requires ValidInput(n, m)
{
  comb2(n - m + 1)
}

// <vc-helpers>
lemma lemma_comb2_nonnegative(n: int)
  requires n >= 0
  ensures comb2(n) >= 0
{
  calc {
    comb2(n);
    == n * (n - 1) / 2;
    { 
      if n >= 1 then 
        assert n * (n - 1) >= 0;
      else 
        assert n == 0 || n == 1;
    }
    >= 0
  }
}

lemma lemma_comb2_monotonic(n: int, m: int)
  requires 0 <= m <= n
  ensures comb2(m) <= comb2(n)
{
  if m == 0 || m == 1 || n == 0 || n == 1 {
    assert comb2(m) == 0 && comb2(n) >= 0;
  } else if m == n {
    assert comb2(m) == comb2(n);
  } else {
    calc {
      comb2(n) - comb2(m);
      (n * (n - 1) - m * (m - 1)) / 2;
      ((n - m) * (n + m - 1)) / 2;
    }
    assert n - m > 0 && n + m - 1 > 0;
  }
}

lemma lemma_MinFriendshipPairs_bounds(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) >= 0
  ensures MinFriendshipPairs(n, m) <= comb2(n)
{
  var k := n / m;
  var p := n % m;
  
  lemma_comb2_nonnegative(k + 1);
  lemma_comb2_nonnegative(k);
  
  assert p * comb2(k + 1) >= 0;
  assert (m - p) * comb2(k) >= 0;
  
  lemma_comb2_monotonic(k + 1, n);
  lemma_comb2_monotonic(k, n);
  
  assert p * comb2(k + 1) <= p * comb2(n);
  assert (m - p) * comb2(k) <= (m - p) * comb2(n);
  
  calc {
    MinFriendshipPairs(n, m);
    p * comb2(k + 1) + (m - p) * comb2(k);
    <= p * comb2(n) + (m - p) * comb2(n);
    == (p + (m - p)) * comb2(n);
    == m * comb2(n);
    <= n * comb2(n) / 2;
    {
      assert comb2(n) == n * (n - 1) / 2;
    }
    <= comb2(n) * n / 2;
  }
}

lemma lemma_MaxFriendshipPairs_bounds(n: int, m: int)
  requires ValidInput(n, m)
  ensures MaxFriendshipPairs(n, m) >= 0
  ensures MaxFriendshipPairs(n, m) <= comb2(n)
{
  lemma_comb2_nonnegative(n - m + 1);
  lemma_comb2_monotonic(n - m + 1, n);
}

lemma lemma_compare_bounds(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) <= MaxFriendshipPairs(n, m)
{
  lemma_MinFriendshipPairs_bounds(n, m);
  lemma_MaxFriendshipPairs_bounds(n, m);
  
  // The key insight: MaxFriendshipPairs creates a single large group of size (n - m + 1)
  // while MinFriendshipPairs distributes people as evenly as possible
  // The minimum case will always have fewer or equal pairs
  var max_group_size := n - m + 1;
  var k := n / m;
  var p := n % m;
  
  if p > 0 {
    assert k + 1 <= max_group_size;
  }
  assert k <= max_group_size;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (min_pairs: int, max_pairs: int)
  requires ValidInput(n, m)
  ensures min_pairs >= 0
  ensures max_pairs >= 0
  ensures min_pairs <= max_pairs
  ensures min_pairs == MinFriendshipPairs(n, m)
  ensures max_pairs == MaxFriendshipPairs(n, m)
// </vc-spec>
// <vc-code>
{
  lemma_MinFriendshipPairs_bounds(n, m);
  lemma_MaxFriendshipPairs_bounds(n, m);
  lemma_compare_bounds(n, m);
  
  min_pairs := MinFriendshipPairs(n, m);
  max_pairs := MaxFriendshipPairs(n, m);
}
// </vc-code>

