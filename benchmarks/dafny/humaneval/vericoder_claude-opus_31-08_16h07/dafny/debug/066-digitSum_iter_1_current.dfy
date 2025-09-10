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
lemma upper_sum_rec_append(s: string, i: nat)
    requires 0 <= i <= |s|
    ensures upper_sum_rec(s[..i]) + upper_sum_rec(s[i..]) == upper_sum_rec(s)
{
    if i == 0 {
        assert s[..0] == "";
        assert s[0..] == s;
    } else if i == |s| {
        assert s[..i] == s;
        assert s[i..] == "";
    } else {
        var prefix := s[..i];
        var suffix := s[i..];
        
        if |prefix| == 0 {
            assert upper_sum_rec(prefix) == 0;
        } else {
            upper_sum_rec_append(s, i-1);
            assert s[..i-1] + [s[i-1]] == s[..i];
            assert upper_sum_rec(s[..i]) == upper_sum_rec(s[..i-1]) + to_int(s[i-1]);
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
        upper_sum_rec_append(s, i+1);
        assert s[..i+1] == s[..i] + [s[i]];
        assert upper_sum_rec(s[..i+1]) == upper_sum_rec(s[..i]) + to_int(s[i]);
        
        res := res + to_int(s[i]);
        i := i + 1;
    }
    
    assert s[..i] == s;
}
// </vc-code>

