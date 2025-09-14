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
lemma count_up_to_bounds(s: string, i: int)
  requires 0 <= i <= |s|
  ensures if i == 0 then count_adjacent_same_pairs_up_to(s, i) == 0 else 0 <= count_adjacent_same_pairs_up_to(s, i) <= i - 1
  decreases i
{
  if i <= 1 {
  } else {
    var prev := count_adjacent_same_pairs_up_to(s, i - 1);
    count_up_to_bounds(s, i - 1);
    var add := if s[i - 1] == s[i - 2] then 1 else 0;
    assert add == 0 || add == 1;
    assert 0 <= add + prev <= 1 + (i - 2);
    assert 1 + (i - 2) == i - 1;
  }
}

lemma count_bounds(s: string, n: int)
  requires n >= 1 && |s| == n
  ensures 0 <= count_adjacent_same_pairs(s, n) <= n - 1
{
  count_up_to_bounds(s, n);
}
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
  result := count_adjacent_same_pairs(s, n);
  count_bounds(s, n);
}
// </vc-code>

