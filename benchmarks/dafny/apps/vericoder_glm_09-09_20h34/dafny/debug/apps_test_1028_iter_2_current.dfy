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
lemma MinFriendshipPairs_nonnegative(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) >= 0
{
  calc {
    MinFriendshipPairs(n, m);
    p * comb2(k + 1) + (m - p) * comb2(k)
    { 
      reveal comb2(); 
      assert k >= 0;
      assert k + 1 >= 1;
      assert p >= 0;
      assert m - p >= 0;
    }
    == p * ((k + 1) * k / 2) + (m - p) * (k * (k - 1) / 2);
    >= 0
  }
}

lemma MaxFriendshipPairs_nonnegative(n: int, m: int)
  requires ValidInput(n, m)
  ensures MaxFriendshipPairs(n, m) >= 0
{
  reveal comb2();
  assert n - m + 1 >= 2;
}

lemma Min_le_Max(n: int, m: int)
  requires ValidInput(n, m)
  ensures MinFriendshipPairs(n, m) <= MaxFriendshipPairs(n, m)
{
  calc {
    MinFriendshipPairs(n, m);
    p * comb2(k + 1) + (m - p) * comb2(k);
    <= p * comb2(n - m + 1) + (m - p) * comb2(n - m + 1);
    { 
      reveal comb2();
    }
    == (p + m - p) * comb2(n - m + 1);
    == m * comb2(n - m + 1);
    <= (n - m + 1) * comb2(n - m + 1);
    { 
      reveal comb2();
      assert (n - m + 1) * ((n - m + 1) * (n - m) / 2) >= (n - m + 1) * (n - m + 1) * (n - m) / (n - m + 1);
    }
    <= comb2(n - m + 1) * (n - m + 1);
    == MaxFriendshipPairs(n, m) * (n - m + 1);
    >= MaxFriendshipPairs(n, m)
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
}
// </vc-code>

