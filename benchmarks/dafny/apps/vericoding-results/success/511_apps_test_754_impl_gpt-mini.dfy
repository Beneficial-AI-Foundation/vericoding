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
lemma step_count(s: string, i: int)
  requires |s| >= i + 1
  requires i >= 1
  ensures count_adjacent_same_pairs_up_to(s, i + 1) == count_adjacent_same_pairs_up_to(s, i) + (if s[i] == s[i-1] then 1 else 0)
  decreases i
{
  // unfold definition (i+1 > 1 since i >= 1)
  assert count_adjacent_same_pairs_up_to(s, i + 1) == (if s[i] == s[i-1] then 1 else 0) + count_adjacent_same_pairs_up_to(s, i);
}

lemma count_nonneg(s: string, i: int)
  requires |s| >= i
  requires i >= 0
  ensures count_adjacent_same_pairs_up_to(s, i) >= 0
  decreases i
{
  if i <= 1 {
    // count is 0
  } else {
    // i > 1
    count_nonneg(s, i - 1);
    assert count_adjacent_same_pairs_up_to(s, i) == (if s[i-1] == s[i-2] then 1 else 0) + count_adjacent_same_pairs_up_to(s, i-1);
    // both summands are >= 0
    assert count_adjacent_same_pairs_up_to(s, i-1) >= 0;
  }
}

lemma count_up_to_bound(s: string, i: int)
  requires |s| >= i
  requires i >= 1
  ensures count_adjacent_same_pairs_up_to(s, i) <= i - 1
  decreases i
{
  if i <= 1 {
    // i == 1, count = 0 <= 0
  } else {
    // i > 1
    count_up_to_bound(s, i - 1);
    assert count_adjacent_same_pairs_up_to(s, i) == (if s[i-1] == s[i-2] then 1 else 0) + count_adjacent_same_pairs_up_to(s, i-1);
    assert count_adjacent_same_pairs_up_to(s, i-1) <= (i - 1) - 1;
    // (if ... then 1 else 0) <= 1
    assert (if s[i-1] == s[i-2] then 1 else 0) + count_adjacent_same_pairs_up_to(s, i-1) <= 1 + ((i - 1) - 1);
    assert 1 + ((i - 1) - 1) == i - 1;
  }
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
  var m := 1;
  var acc := 0;
  while m < n
    invariant 1 <= m <= n
    invariant acc == count_adjacent_same_pairs_up_to(s, m)
  {
    if s[m] == s[m-1] {
      acc := acc + 1;
    }
    step_count(s, m);
    m := m + 1;
  }
  result := acc;
  // Establish numeric postconditions using lemmas
  count_nonneg(s, n);
  count_up_to_bound(s, n);
}
// </vc-code>

