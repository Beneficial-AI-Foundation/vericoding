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
lemma upper_sum_rec_nonneg(s: string)
  ensures upper_sum_rec(s) >= 0
{
  if |s| == 0 {
    // Base case: empty string
  } else {
    // Inductive case
    upper_sum_rec_nonneg(s[1..]);
    assert to_int(s[0]) >= 0;
    assert upper_sum_rec(s[1..]) >= 0;
  }
}

lemma upper_sum_rec_prefix(s: string, i: int)
  requires 0 <= i <= |s|
  ensures upper_sum_rec(s[..i]) + upper_sum_rec(s[i..]) == upper_sum_rec(s)
  decreases i
{
  if i == 0 {
    assert s[..i] == "";
    assert s[i..] == s;
    assert upper_sum_rec(s[..i]) == 0;
  } else if i == |s| {
    assert s[..i] == s;
    assert s[i..] == "";
    assert upper_sum_rec(s[i..]) == 0;
  } else {
    upper_sum_rec_prefix(s, i - 1);
    assert upper_sum_rec(s[..i-1]) + upper_sum_rec(s[i-1..]) == upper_sum_rec(s);
    assert upper_sum_rec(s[i-1..]) == to_int(s[i-1]) + upper_sum_rec(s[i..]);
    assert s[..i] == s[..i-1] + [s[i-1]];
    assert upper_sum_rec(s[..i]) == to_int(s[0]) + upper_sum_rec(s[..i][1..]);
    assert s[..i][1..] == s[1..i];
    assert upper_sum_rec(s[..i]) == to_int(s[0]) + upper_sum_rec(s[1..i]);
  }
}

lemma upper_sum_rec_step(s: string, i: int)
  requires 0 <= i < |s|
  ensures upper_sum_rec(s[..i+1]) == upper_sum_rec(s[..i]) + to_int(s[i])
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == "";
    assert upper_sum_rec(s[..1]) == to_int(s[0]) + upper_sum_rec("");
    assert upper_sum_rec("") == 0;
  } else {
    assert s[..i+1] == s[..i] + [s[i]];
    assert upper_sum_rec(s[..i+1]) == to_int(s[0]) + upper_sum_rec(s[..i+1][1..]);
    assert s[..i+1][1..] == s[1..i+1];
    assert upper_sum_rec(s[..i]) == to_int(s[0]) + upper_sum_rec(s[1..i]);
    upper_sum_rec_step(s[1..], i - 1);
    assert upper_sum_rec(s[1..][..i]) == upper_sum_rec(s[1..][..i-1]) + to_int(s[1..][i-1]);
    assert s[1..][..i] == s[1..i];
    assert s[1..][..i-1] == s[1..i-1];
    assert s[1..][i-1] == s[i];
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def digitSum(string: str) -> Nat
Write a function that takes a string as input and returns the sum of the upper characters only' ASCII codes.
*/
// </vc-description>

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
    upper_sum_rec_step(s, i);
    res := res + to_int(s[i]);
    i := i + 1;
  }
  assert i == |s|;
  assert s[..i] == s;
}
// </vc-code>

