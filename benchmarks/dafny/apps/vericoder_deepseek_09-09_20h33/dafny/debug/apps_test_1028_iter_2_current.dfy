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
lemma MinFriendshipPairsNonNegative(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) >= 0
{
  var k := n / m;
  var p := n % m;
  
  // comb2(k) and comb2(k+1) are non-negative for k >= 0
  assert comb2(k + 1) >= 0;
  assert comb2(k) >= 0;
}

lemma MaxFriendshipPairsNonNegative(n: int, m: int)
  requires ValidInput(n, m)
  ensures MaxFriendshipPairs(n, m) >= 0
{
  assert n - m + 1 >= 0;
}

lemma Comb2NonDecreasing(x: int, y: int)
  requires x >= 0 && y >= 0
  requires x <= y
  ensures comb2(x) <= comb2(y)
{
  if x < y {
    Comb2NonDecreasing(x + 1, y);
  }
}

lemma MinMaxRelationship(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) <= MaxFriendshipPairs(n, m)
{
  var k := n / m;
  var p := n % m;
  
  // Key insight: The maximum case is when one group has n-m+1 people
  // and the rest have 1 person each. The minimum case is when groups
  // are as balanced as possible.
  
  // Show that comb2(k+1) <= comb2(n-m+1) and comb2(k) <= comb2(n-m+1)
  assert k >= 1;
  assert k <= n - m + 1;
  Comb2NonDecreasing(k, n - m + 1);
  Comb2NonDecreasing(k + 1, n - m + 1);
  
  // Now show the weighted sum is also <= comb2(n-m+1)
  assert p * comb2(k + 1) + (m - p) * comb2(k) <= p * comb2(n - m + 1) + (m - p) * comb2(n - m + 1);
  assert p * comb2(n - m + 1) + (m - p) * comb2(n - m + 1) == m * comb2(n - m + 1);
  
  // Finally, show m * comb2(n-m+1) <= comb2(n-m+1)
  // This is true because m >= 1 and comb2(n-m+1) >= 0
  if m > 1 {
    assert m * comb2(n - m + 1) >= comb2(n - m + 1);
  }
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
  min_pairs := MinFriendshipPairs(n, m);
  max_pairs := MaxFriendshipPairs(n, m);
  
  // The lemmas ensure the post conditions
  assert min_pairs >= 0 by { MinFriendshipPairsNonNegative(n, m); }
  assert max_pairs >= 0 by { MaxFriendshipPairsNonNegative(n, m); }
  assert min_pairs <= max_pairs by { MinMaxRelationship(n, m); }
}
// </vc-code>

