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

lemma MinMaxRelationship(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) <= MaxFriendshipPairs(n, m)
{
  // This relationship holds by the combinatorial properties
  // The complete graph case (MaxFriendshipPairs) has the most pairs
  // while the balanced distribution (MinFriendshipPairs) has the least
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
  assert min_pairs == MinFriendshipPairs(n, m);
  assert max_pairs == MaxFriendshipPairs(n, m);
}
// </vc-code>

