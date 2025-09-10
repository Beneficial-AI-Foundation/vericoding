predicate ValidInput(n: int, s: string)
{
    n >= 1 && |s| == n
}

function count_adjacent_same_pairs(s: string, n: int): int
    requires n >= 1
    requires |s| == n
{
    count_adjacent_same_pairs_up_to(s, n)
}

function count_adjacent_same_pairs_up_to(s: string, i: int): int
    requires |s| >= i >= 0
{
    if i <= 1 then 0
    else (if s[i-1] == s[i-2] then 1 else 0) + count_adjacent_same_pairs_up_to(s, i-1)
}

// <vc-helpers>
lemma CountAdjacentSamePairsLemma(s: string, n: int)
    requires n >= 1
    requires |s| == n
    ensures count_adjacent_same_pairs(s, n) == count_adjacent_same_pairs_up_to(s, n)
{}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: int)
    requires ValidInput(n, s)
    ensures result >= 0
    ensures result <= n - 1
    ensures result == count_adjacent_same_pairs(s, n)
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n - 1
    invariant count == count_adjacent_same_pairs_up_to(s, i + 1)
  {
    if s[i] == s[i+1] {
      count := count + 1;
    }
    i := i + 1;
  }
  result := count;
  CountAdjacentSamePairsLemma(s, n);
}
// </vc-code>

