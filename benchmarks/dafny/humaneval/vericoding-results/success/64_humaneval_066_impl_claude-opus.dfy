// <vc-preamble>

function sumOfUppercaseASCII(s: string): int
    ensures sumOfUppercaseASCII(s) >= 0
{
    if |s| == 0 then 0
    else 
        var c := s[0];
        var rest := sumOfUppercaseASCII(s[1..]);
        if 'A' <= c && c <= 'Z' then (c as int) + rest
        else rest
}
lemma sumOfUppercaseASCII_lemma(s: string, c: char)
    ensures sumOfUppercaseASCII(s + [c]) == 
            if 'A' <= c && c <= 'Z' then sumOfUppercaseASCII(s) + (c as int)
            else sumOfUppercaseASCII(s)
{
    if |s| == 0 {
        assert s + [c] == [c];
        assert sumOfUppercaseASCII([c]) == (if 'A' <= c && c <= 'Z' then (c as int) else 0);
        assert sumOfUppercaseASCII(s) == 0;
    } else {
        assert (s + [c])[0] == s[0];
        assert (s + [c])[1..] == s[1..] + [c];
        sumOfUppercaseASCII_lemma(s[1..], c);
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method digitSum(s: string) returns (result: int)
    ensures result >= 0
    ensures result == sumOfUppercaseASCII(s)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant result == sumOfUppercaseASCII(s[..i])
  {
    var c := s[i];
    if 'A' <= c && c <= 'Z' {
      result := result + (c as int);
    }
    sumOfUppercaseASCII_lemma(s[..i], c);
    assert s[..i+1] == s[..i] + [c];
    i := i + 1;
  }
  assert s[..|s|] == s;
}
// </vc-code>
