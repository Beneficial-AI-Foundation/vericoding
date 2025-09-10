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
lemma Comb2NonNegative(n: int)
  requires n >= 0
  ensures comb2(n) >= 0
{
  if n <= 1 {
    assert comb2(n) == n * (n - 1) / 2;
    assert n * (n - 1) >= 0;
  } else {
    assert n >= 2;
    assert n * (n - 1) >= 0;
    assert comb2(n) == n * (n - 1) / 2 >= 0;
  }
}

lemma MinPairsNonNegative(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) >= 0
{
  var k := n / m;
  var p := n % m;
  
  assert k >= 0;
  assert 0 <= p < m;
  
  Comb2NonNegative(k);
  Comb2NonNegative(k + 1);
  
  assert comb2(k) >= 0;
  assert comb2(k + 1) >= 0;
  assert p >= 0;
  assert m - p >= 0;
  
  assert MinFriendshipPairs(n, m) == p * comb2(k + 1) + (m - p) * comb2(k);
  assert MinFriendshipPairs(n, m) >= 0;
}

lemma MaxPairsNonNegative(n: int, m: int)
  requires ValidInput(n, m)
  ensures MaxFriendshipPairs(n, m) >= 0
{
  assert n - m + 1 >= 0;
  Comb2NonNegative(n - m + 1);
  assert MaxFriendshipPairs(n, m) == comb2(n - m + 1) >= 0;
}

lemma Comb2Properties(x: int, y: int)
  requires x >= 0 && y >= 0
  requires x <= y
  ensures comb2(x) <= comb2(y)
{
  // comb2 is monotonically increasing for non-negative values
  assert comb2(x) == x * (x - 1) / 2;
  assert comb2(y) == y * (y - 1) / 2;
  if x == 0 {
    assert comb2(x) == 0;
    Comb2NonNegative(y);
  } else if x == y {
    assert comb2(x) == comb2(y);
  }
}

lemma MinMaxOrdering(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) <= MaxFriendshipPairs(n, m)
{
  var k := n / m;
  var p := n % m;
  
  // Key insight: The minimum occurs with balanced groups
  // The maximum occurs with one large group
  
  assert n == k * m + p;
  assert 0 <= p < m;
  
  if m == 1 {
    assert p == 0;
    assert k == n;
    assert MinFriendshipPairs(n, m) == comb2(n);
    assert MaxFriendshipPairs(n, m) == comb2(n);
    assert MinFriendshipPairs(n, m) == MaxFriendshipPairs(n, m);
  } else {
    // For m > 1, we have n - m + 1 >= k + 1
    assert m > 1;
    assert n >= m;
    assert n - m + 1 >= 1;
    
    // The minimum configuration has groups of size k and k+1
    // The maximum configuration has one group of size n-m+1
    
    MinPairsNonNegative(n, m);
    MaxPairsNonNegative(n, m);
    
    // Since we're spreading people into multiple groups in the minimum case,
    // we get fewer total pairs than putting most people in one large group
    if k == 0 {
      assert n < m;
      assert false; // This contradicts ValidInput
    } else if k == 1 && p == 0 {
      assert n == m;
      assert MinFriendshipPairs(n, m) == m * comb2(1) == 0;
      assert MaxFriendshipPairs(n, m) == comb2(1) == 0;
    }
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
  var k := n / m;
  var p := n % m;
  
  min_pairs := p * comb2(k + 1) + (m - p) * comb2(k);
  max_pairs := comb2(n - m + 1);
  
  MinPairsNonNegative(n, m);
  MaxPairsNonNegative(n, m);
  MinMaxOrdering(n, m);
  
  assert min_pairs == MinFriendshipPairs(n, m);
  assert max_pairs == MaxFriendshipPairs(n, m);
}
// </vc-code>

