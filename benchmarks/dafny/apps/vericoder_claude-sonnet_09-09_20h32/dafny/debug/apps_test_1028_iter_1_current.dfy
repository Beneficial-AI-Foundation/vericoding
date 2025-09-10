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
lemma MinMaxRelation(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) <= MaxFriendshipPairs(n, m)
{
  var k := n / m;
  var p := n % m;
  var min_val := p * comb2(k + 1) + (m - p) * comb2(k);
  var max_val := comb2(n - m + 1);
  
  assert min_val >= 0;
  assert max_val >= 0;
  
  if m == 1 {
    assert min_val == comb2(n) && max_val == comb2(n);
  } else if m == n {
    assert min_val == 0 && max_val == 0;
  } else {
    assert min_val <= max_val;
  }
}

lemma MinFriendshipPairsNonNegative(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) >= 0
{
  var k := n / m;
  var p := n % m;
  assert k >= 0;
  assert 0 <= p < m;
  assert comb2(k) >= 0;
  assert comb2(k + 1) >= 0;
}

lemma MaxFriendshipPairsNonNegative(n: int, m: int)
  requires ValidInput(n, m)
  ensures MaxFriendshipPairs(n, m) >= 0
{
  assert n - m + 1 >= 0;
  assert comb2(n - m + 1) >= 0;
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
  MinFriendshipPairsNonNegative(n, m);
  MaxFriendshipPairsNonNegative(n, m);
  MinMaxRelation(n, m);
  
  min_pairs := MinFriendshipPairs(n, m);
  max_pairs := MaxFriendshipPairs(n, m);
}
// </vc-code>

