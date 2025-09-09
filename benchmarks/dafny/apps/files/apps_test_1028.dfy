Given n participants split into m teams where each team has at least one participant,
find the minimum and maximum possible number of friendship pairs that can form.
Friendship pairs are formed between all participants within the same team.

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

method solve(n: int, m: int) returns (min_pairs: int, max_pairs: int)
  requires ValidInput(n, m)
  ensures min_pairs >= 0
  ensures max_pairs >= 0
  ensures min_pairs <= max_pairs
  ensures min_pairs == MinFriendshipPairs(n, m)
  ensures max_pairs == MaxFriendshipPairs(n, m)
{
  var k := n / m;
  var p := n % m;

  // Minimum: distribute as evenly as possible
  // p teams get k+1 participants, (m-p) teams get k participants
  var tmpCall1 := comb2(k + 1);
  var tmpCall2 := comb2(k);
  min_pairs := p * tmpCall1 + (m - p) * tmpCall2;

  // Maximum: put as many as possible in one team
  // One team gets (n-m+1) participants, others get 1 each
  var tmpCall3 := comb2(n - m + 1);
  max_pairs := tmpCall3;
}
