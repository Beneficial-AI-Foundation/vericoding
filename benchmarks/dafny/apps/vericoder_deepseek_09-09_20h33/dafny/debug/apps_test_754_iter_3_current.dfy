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
lemma count_adjacent_same_pairs_up_to_lemma(s: string, i: int, j: int)
  requires |s| >= i >= j >= 0
  ensures count_adjacent_same_pairs_up_to(s, i) - count_adjacent_same_pairs_up_to(s, j) ==
          count_adjacent_same_pairs_up_to(s[j..], i-j)
  decreases i - j
{
  if i > j {
    count_adjacent_same_pairs_up_to_lemma(s, i-1, j);
    var sub := s[j..];
    assert |sub| == |s| - j;
    assert i - j <= |sub|;
    if i - j > 1 {
      assert sub[(i-1)-j] == s[i-1];
      assert sub[(i-2)-j] == s[i-2];
    }
  }
}

lemma count_empty_string_lemma()
  ensures forall i :: 0 <= i <= 0 ==> count_adjacent_same_pairs_up_to("", i) == 0
{
}

lemma count_adjacent_same_pairs_up_to_zero(s: string, i: int)
  requires |s| >= i >= 0
  ensures count_adjacent_same_pairs_up_to(s, i) >= 0
  decreases i
{
  if i > 1 {
    count_adjacent_same_pairs_up_to_zero(s, i-1);
  }
}

lemma count_adjacent_same_pairs_up_to_bound(s: string, i: int)
  requires |s| >= i >= 0
  ensures count_adjacent_same_pairs_up_to(s, i) <= if i <= 1 then 0 else i-1
  decreases i
{
  if i > 1 {
    count_adjacent_same_pairs_up_to_bound(s, i-1);
  }
}
// </vc-helpers>
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
  result := 0;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant result == count_adjacent_same_pairs_up_to(s, i)
    invariant result >= 0 && result <= i - 1
  {
    if s[i-1] == s[i] {
      result := result + 1;
    }
    i := i + 1;
  }
  assert i == n;
  assert result == count_adjacent_same_pairs_up_to(s, n);
}
// </vc-code>

