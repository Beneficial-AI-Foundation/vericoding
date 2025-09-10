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
lemma concat_upper_sum(a: string, b: string)
  ensures upper_sum_rec(a + b) == upper_sum_rec(a) + upper_sum_rec(b)
  decreases |a|
{
  if |a| == 0 {
    // a is empty string
    assert a == "";
    assert a + b == b;
    assert upper_sum_rec(a + b) == upper_sum_rec(b);
    assert upper_sum_rec(a) == 0;
  } else {
    // unfold definitions
    assert upper_sum_rec(a + b) == to_int((a + b)[0]) + upper_sum_rec((a + b)[1..]);
    assert upper_sum_rec(a) == to_int(a[0]) + upper_sum_rec(a[1..]);
    // index and slice properties for concatenation
    assert (a + b)[0] == a[0];
    assert (a + b)[1..] == a[1..] + b;
    // apply induction on a[1..]
    concat_upper_sum(a[1..], b);
    // now combine equalities
    assert upper_sum_rec((a + b)[1..]) == upper_sum_rec(a[1..]) + upper_sum_rec(b);
    assert upper_sum_rec(a + b) == to_int(a[0]) + upper_sum_rec(a[1..]) + upper_sum_rec(b);
    assert upper_sum_rec(a + b) == upper_sum_rec(a) + upper_sum_rec(b);
  }
}

lemma upper_sum_single(t: string)
  requires |t| == 1
  ensures upper_sum_rec(t) == to_int(t[0])
{
  // unfold and simplify
  assert upper_sum_rec(t) == to_int(t[0]) + upper_sum_rec(t[1..]);
  assert t[1..] == "";
  assert upper_sum_rec(t[1..]) == 0;
  assert upper_sum_rec(t) == to_int(t[0]);
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
    var idx := i;
    res := res + to_int(s[idx]);
    // show that res now equals upper_sum_rec(s[..idx+1])
    // upper_sum_rec(s[..idx+1]) == upper_sum_rec(s[..idx]) + upper_sum_rec(s[idx..idx+1])
    concat_upper_sum(s[..idx], s[idx..idx+1]);
    // upper_sum_rec of single-character slice equals to_int of that char
    upper_sum_single(s[idx..idx+1]);
    // combine using the loop invariant res == upper_sum_rec(s[..idx])
    assert res == upper_sum_rec(s[..idx]) + upper_sum_rec(s[idx..idx+1]);
    assert res == upper_sum_rec(s[..idx+1]);
    i := idx + 1;
  }
}
// </vc-code>

