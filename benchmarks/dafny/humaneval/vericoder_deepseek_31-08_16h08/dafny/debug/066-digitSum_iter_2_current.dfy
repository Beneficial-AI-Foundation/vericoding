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
lemma {:induction s} UpperSumRecLemma(s: string)
  ensures upper_sum_rec(s) >= 0
{
  if |s| != 0 {
    UpperSumRecLemma(s[1..]);
  }
}

lemma UpperSumRecSliceLemma(s: string, i: int)
  requires 0 <= i <= |s|
  ensures upper_sum_rec(s[0..i]) + upper_sum_rec(s[i..]) == upper_sum_rec(s)
{
  if i == 0 {
    assert s[0..0] == "";
    assert upper_sum_rec(s[0..0]) == 0;
  } else {
    UpperSumRecSliceLemma(s[0..|s|-1], i-1);
    assert s[0..i] == s[0..i-1] + [s[i-1]];
    assert upper_sum_rec(s[0..i]) == upper_sum_rec(s[0..i-1]) + to_int(s[i-1]);
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
    invariant res == upper_sum_rec(s[0..i])
  {
    res := res + to_int(s[i]);
    i := i + 1;
    // Prove that upper_sum_rec(s[0..i]) == res after update
    assert s[0..i] == s[0..i-1] + [s[i-1]];
    assert upper_sum_rec(s[0..i]) == upper_sum_rec(s[0..i-1]) + to_int(s[i-1]);
    assert upper_sum_rec(s[0..i]) == old(res) + to_int(s[i-1]);
    assert res == old(res) + to_int(s[i-1]);
  }
  assert i == |s|;
}
// </vc-code>

