function count_a(s: string): int
    ensures count_a(s) >= 0
    ensures count_a(s) <= |s|
{
    if |s| == 0 then 0
    else (if s[0] == 'a' then 1 else 0) + count_a(s[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

predicate ValidInput(s: string)
{
    |s| >= 1 && exists i :: 0 <= i < |s| && s[i] == 'a'
}

predicate IsGoodString(s: string)
{
    |s| > 0 && count_a(s) > |s| / 2
}

// <vc-helpers>
lemma CountA_PositiveIfContainsA(s: string)
  requires exists i :: 0 <= i < |s| && s[i] == 'a'
  ensures count_a(s) >= 1
  decreases |s|
{
  if |s| == 0 {
  } else if s[0] == 'a' {
    assert count_a(s) == 1 + count_a(s[1..]);
    assert count_a(s) >= 1;
  } else {
    var i :| 0 <= i < |s| && s[i] == 'a';
    if i == 0 {
      assert s[0] == 'a';
      assert false;
    }
    assert i >= 1;
    assert |s| > 0;
    assert |s[1..]| == |s| - 1;
    assert 0 <= i - 1 < |s[1..]|;
    assert s[1..][i-1] == s[i];
    assert s[1..][i-1] == 'a';
    assert exists j :: 0 <= j < |s[1..]| && s[1..][j] == 'a';
    CountA_PositiveIfContainsA(s[1..]);
    assert count_a(s) == count_a(s[1..]);
    assert count_a(s) >= 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result >= 1
    ensures result <= |s|
    ensures result == min(2 * count_a(s) - 1, |s|)
// </vc-spec>
// <vc-code>
{
  CountA_PositiveIfContainsA(s);
  result := min(2 * count_a(s) - 1, |s|);
}
// </vc-code>

