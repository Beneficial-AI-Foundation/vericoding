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
lemma UpperSumRecNonNegative(s: string)
  ensures upper_sum_rec(s) >= 0
{
  if |s| == 0 {
    assert upper_sum_rec(s) == 0;
  } else {
    var remaining := upper_sum_rec(s[1..]);
    UpperSumRecNonNegative(s[1..]);
    assert remaining >= 0;
    var current := to_int(s[0]);
    assert current >= 0;
    assert upper_sum_rec(s) == current + remaining;
  }
}

lemma UpperSumRecAppend(s: string, i: int)
  requires 0 <= i < |s|
  ensures upper_sum_rec(s[..i+1]) == upper_sum_rec(s[..i]) + to_int(s[i])
{
  if i == 0 {
    assert s[..1] == s[0..1];
    assert upper_sum_rec(s[..1]) == to_int(s[0]);
    assert s[..0] == "";
    assert upper_sum_rec(s[..0]) == 0;
    assert upper_sum_rec(s[..1]) == upper_sum_rec(s[..0]) + to_int(s[0]);
  } else {
    assert s[..i+1] == s[0..i+1];
    assert s[..i+1] == s[0] + s[1..i+1];
    assert s[1..][..i] == s[1..i+1];
    calc {
      upper_sum_rec(s[..i+1]);
      to_int(s[0]) + upper_sum_rec(s[1..][..i]);
      { UpperSumRecAppend(s[1..], i-1); }
      to_int(s[0]) + upper_sum_rec(s[1..][..i-1]) + to_int(s[i]);
      { assert s[1..][..i-1] == s[1..i]; }
      to_int(s[0]) + upper_sum_rec(s[1..i]) + to_int(s[i]);
      { assert s[..i] == s[0..i]; }
      upper_sum_rec(s[..i]) + to_int(s[i]);
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
method DigitSum(s: string) returns (res: int)
{
  var sum := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant sum == upper_sum_rec(s[..i])
  {
    sum := sum + to_int(s[i]);
    i := i + 1;
    if i <= |s| {
      if i < |s| {
        UpperSumRecAppend(s, i-1);
      } else {
        assert s[..i] == s;
      }
    }
  }
  res := sum;
  assert s[..i] == s;
  assert res == upper_sum_rec(s);
}
// </vc-code>
