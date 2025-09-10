predicate ValidInput(s: string) {
    |s| == 4 && forall i :: 0 <= i < |s| ==> s[i] == '+' || s[i] == '-'
}

function CountChar(s: string, c: char): int
{
    if |s| == 0 then 0
    else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function CalculateSum(s: string): int
    requires ValidInput(s)
{
    CountChar(s, '+') - CountChar(s, '-')
}

// <vc-helpers>
lemma CountChar_last(t: string, c: char)
    requires |t| > 0
    ensures CountChar(t, c) == CountChar(t[..|t|-1], c) + (if t[|t|-1] == c then 1 else 0)
    decreases |t|
{
    if |t| == 1 {
        // CountChar of single-char string equals 0 + (if that char equals c then 1 else 0)
        assert CountChar(t, c) == (if t[0] == c then 1 else 0);
        assert CountChar(t[..|t|-1], c) == CountChar("", c);
        assert CountChar("", c) == 0;
    } else {
        var tail := t[1..];
        CountChar_last(tail, c);
        // Unfold definitions
        assert CountChar(t, c) == (if t[0] == c then 1 else 0) + CountChar(tail, c);
        assert CountChar(tail, c) == CountChar(t[1..|t|-1], c) + (if t[|t|-1] == c then 1 else 0);
        assert CountChar(t[..|t|-1], c) == (if t[0] == c then 1 else 0) + CountChar(t[1..|t|-1], c);
    }
    // Combine to get the desired equality
    assert CountChar(t, c) == CountChar(t[..|t|-1], c) + (if t[|t|-1] == c then 1 else 0);
}

lemma CountChar_step(s: string, i: int, c: char)
    requires 0 <= i < |s|
    ensures CountChar(s[..i+1], c) == CountChar(s[..i], c) + (if s[i] == c then 1 else 0)
{
    var t := s[..i+1];
    assert |t| == i + 1;
    assert |t| > 0;
    CountChar_last(t, c);
    assert |t| - 1 == i;
    assert t[..|t|-1] == s[..i];
    assert t[|t|-1] == s[i];
    assert CountChar(t, c) == CountChar(t[..|t|-1], c) + (if t[|t|-1] == c then 1 else 0);
    assert CountChar(s[..i+1], c) == CountChar(s[..i], c) + (if s[i] == c then 1 else 0);
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == CalculateSum(s)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var plus := 0;
  var minus := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant plus == CountChar(s[..i], '+')
    invariant minus == CountChar(s[..i], '-')
    decreases |s| - i
  {
    var ch := s[i];
    if ch == '+' {
      var oldPlus := plus;
      plus := plus + 1;
      CountChar_step(s, i, '+');
      assert CountChar(s[..i+1], '+') == CountChar(s[..i], '+') + (if s[i] == '+' then 1 else 0);
      assert oldPlus == CountChar(s[..i], '+');
      assert plus == CountChar(s[..i+1], '+');
      CountChar_step(s, i, '-');
      assert CountChar(s[..i+1], '-') == CountChar(s[..i], '-') + (if s[i] == '-' then 1 else 0);
      assert (if s[i] == '-' then 1 else 0) == 0;
      assert minus == CountChar(s[..i+1], '-');
    } else {
      var oldMinus := minus;
      minus := minus + 1;
      CountChar_step(s, i, '-');
      assert CountChar(s[..i+1], '-') == CountChar(s[..i], '-') + (if s[i] == '-' then 1 else 0);
      assert oldMinus == CountChar(s[..i], '-');
      assert minus == CountChar(s[..i+1], '-');
      CountChar_step(s, i, '+');
      assert CountChar(s[..i+1], '+') == CountChar(s[..i], '+') + (if s[i] == '+' then 1 else 0);
      assert (if s[i] == '+' then 1 else 0) == 0;
      assert plus == CountChar(s[..i+1], '+');
    }
    i := i + 1;
  }
  assert i == |s|;
  assert s[..i] == s;
  assert plus == CountChar(s, '+');
  assert minus == CountChar(s, '-');
  result := plus - minus;
}
// </vc-code>

