function upper_sum_rec(s: string): int
  // post-conditions-start
  ensures upper_sum_rec(s) >= 0
  // post-conditions-end
{
  // impl-start
  if |s| == 0 then
    0
  else
    var remaining := upper_sum_rec(s[1..]);
    to_int(s[0]) + remaining
  // impl-end
}
function to_int(c: char): int
    ensures 'A' <= c <= 'Z' ==> to_int(c) == c as int
    ensures c < 'A' || c > 'Z' ==> to_int(c) == 0
{
    if 'A' <= c <= 'Z' then c as int else 0
}

// <vc-helpers>
lemma upper_sum_rec_nonnegative(s: string)
    ensures upper_sum_rec(s) >= 0
{
    if |s| == 0 {
        // base case: empty string
    } else {
        // inductive case
        upper_sum_rec_nonnegative(s[1..]);
        assert to_int(s[0]) >= 0;
        assert upper_sum_rec(s[1..]) >= 0;
    }
}

lemma upper_sum_rec_prefix_property(s: string, i: int)
    requires 0 <= i < |s|
    ensures upper_sum_rec(s[..i+1]) == upper_sum_rec(s[..i]) + to_int(s[i])
{
    if i == 0 {
        assert s[..1] == [s[0]];
        assert s[..0] == [];
        assert upper_sum_rec(s[..0]) == 0;
        assert upper_sum_rec(s[..1]) == to_int(s[0]) + upper_sum_rec(s[1..1]);
        assert s[1..1] == [];
        assert upper_sum_rec(s[1..1]) == 0;
    } else {
        var prefix_i := s[..i];
        var prefix_i_plus_1 := s[..i+1];
        assert prefix_i_plus_1 == prefix_i + [s[i]];
        assert upper_sum_rec(prefix_i_plus_1) == to_int(s[0]) + upper_sum_rec(prefix_i_plus_1[1..]);
        assert upper_sum_rec(prefix_i) == to_int(s[0]) + upper_sum_rec(prefix_i[1..]);
        assert prefix_i_plus_1[1..] == s[1..i+1];
        assert prefix_i[1..] == s[1..i];
        if i >= 1 {
            upper_sum_rec_prefix_property(s[1..], i-1);
            assert upper_sum_rec(s[1..i+1]) == upper_sum_rec(s[1..i]) + to_int(s[1..][i-1]);
            assert s[1..][i-1] == s[i];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method upper_sum(s: string) returns (res: int)
    // post-conditions-start
    ensures res == upper_sum_rec(s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    res := 0;
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant res == upper_sum_rec(s[..i])
    {
        upper_sum_rec_prefix_property(s, i);
        res := res + to_int(s[i]);
        i := i + 1;
    }
    assert i == |s|;
    assert s[..i] == s;
}
// </vc-code>

