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
  var cnt := 0;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= cnt
    invariant cnt <= i - 1
    invariant cnt == count_adjacent_same_pairs_up_to(s, i)
    decreases n - i
  {
    if s[i] == s[i - 1] {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  result := cnt;
}
// </vc-code>

