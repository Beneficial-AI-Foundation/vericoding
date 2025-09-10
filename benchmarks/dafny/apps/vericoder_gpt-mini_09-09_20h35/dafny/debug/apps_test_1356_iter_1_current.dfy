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
lemma CountA_at_least_one_from_exists(s: string)
    requires exists i :: 0 <= i < |s| && s[i] == 'a'
    ensures count_a(s) >= 1
    decreases |s|
{
    if |s| == 0 {
        // impossible due to requires
        assert false;
    }
    // obtain a witness index where s[i] == 'a'
    var i :| 0 <= i < |s| && s[i] == 'a';
    if i == 0 {
        // s[0] == 'a' so count_a(s) = 1 + count_a(s[1..]) >= 1
        assert s[0] == 'a';
        assert count_a(s) >= 1;
    } else {
        // shift to substring s1 = s[1..], witness at i-1
        var s1 := s[1..];
        assert 0 <= i - 1 < |s1| && s1[i - 1] == 'a';
        CountA_at_least_one_from_exists(s1);
        assert count_a(s1) >= 1;
        if s[0] == 'a' {
            // then count_a(s) = 1 + count_a(s1) >= 1
            assert count_a(s) >= 1;
        } else {
            // s[0] != 'a' so count_a(s) = count_a(s1)
            assert count_a(s) == count_a(s1);
            assert count_a(s) >= 1;
        }
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
  var ca := count_a(s);
  // from ValidInput(s) we know there is at least one 'a'
  CountA_at_least_one_from_exists(s);
  if 2 * ca - 1 <= |s| {
    result := 2 * ca - 1;
  } else {
    result := |s|;
  }
}
// </vc-code>

