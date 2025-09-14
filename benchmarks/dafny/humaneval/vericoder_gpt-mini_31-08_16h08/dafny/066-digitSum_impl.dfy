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
    invariant res + upper_sum_rec(s[i..]) == upper_sum_rec(s)
  {
    var idx := i;
    var oldRes := res;
    // s[idx..] is non-empty because idx < |s|
    assert |s[idx..]| > 0;
    // unfold definition for the non-empty suffix s[idx..]
    assert upper_sum_rec(s[idx..]) == to_int((s[idx..])[0]) + upper_sum_rec((s[idx..])[1..]);
    assert (s[idx..])[0] == s[idx];
    assert (s[idx..])[1..] == s[idx+1..];
    // update res by adding the integer value of the current character
    res := oldRes + to_int(s[idx]);
    // show the invariant holds after the update
    assert res + upper_sum_rec(s[idx+1..]) == oldRes + to_int(s[idx]) + upper_sum_rec(s[idx+1..]);
    assert res + upper_sum_rec(s[idx+1..]) == oldRes + upper_sum_rec(s[idx..]);
    assert oldRes + upper_sum_rec(s[idx..]) == upper_sum_rec(s);
    i := idx + 1;
  }
}
// </vc-code>

