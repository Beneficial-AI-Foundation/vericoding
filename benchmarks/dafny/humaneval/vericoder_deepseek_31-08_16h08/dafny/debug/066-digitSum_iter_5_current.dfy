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
    UpperSumRecSliceLemma(s, i-1);
    calc {
      upper_sum_rec(s[0..i]);
      == { assert s[0..i] == s[0..i-1] + [s[i-1]]; }
      upper_sum_rec(s[0..i-1] + [s[i-1]]);
      == // Definition of upper_sum_rec for non-empty strings
      to_int(s[i-1]) + upper_sum_rec(s[0..i-1][1..]);
      == { assert s[0..i-1][1..] == s[1..i]; }
      to_int(s[i-1]) + upper_sum_rec(s[1..i]);
      ==
      upper_sum_rec(s[0..i-1]) + to_int(s[i-1]);
    }
  }
}

lemma UpperSumRecStepLemma(s: string, i: int)
  requires 0 <= i < |s|
  ensures upper_sum_rec(s[0..i+1]) == upper_sum_rec(s[0..i]) + to_int(s[i])
{
  calc {
    upper_sum_rec(s[0..i+1]);
    == { assert s[0..i+1] == s[0..i] + [s[i]]; }
    upper_sum_rec(s[0..i] + [s[i]]);
    == // Definition of upper_sum_rec
    to_int((s[0..i] + [s[i]])[0]) + upper_sum_rec((s[0..i] + [s[i]])[1..]);
    == { assert (s[0..i] + [s[i]])[0] == s[0] if i > 0 else s[i]; }
    { if i > 0 {
        assert s[0..i] != "";
      } else {
        assert s[0..0] == "";
      }
    }
    upper_sum_rec(s[0..i]) + to_int(s[i]);
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
    calc {
      res + to_int(s[i]);
      == 
      upper_sum_rec(s[0..i]) + to_int(s[i]);
      == { UpperSumRecStepLemma(s, i); }
      upper_sum_rec(s[0..i+1]);
    }
    res := res + to_int(s[i]);
    i := i + 1;
  }
}
// </vc-code>

