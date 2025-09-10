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
        // CountChar(t,c) = (if t[0]==c then 1 else 0) + CountChar(t[1..],c) and CountChar(empty)=0
        assert CountChar(t, c) == (if t[0] == c then 1 else 0) + CountChar(t[1..], c);
        assert CountChar(t[1..], c) == 0;
        assert CountChar(t[..|t|-1], c) == 0;
        assert CountChar(t, c) == CountChar(t[..|t|-1], c) + (if t[|t|-1] == c then 1 else 0);
    } else {
        // Unfold definition for t
        assert CountChar(t, c) == (if t[0] == c then 1 else 0) + CountChar(t[1..], c);
        // Apply induction to tail
        CountChar_last(t[1..], c);
        // From IH: CountChar(t[1..], c) == CountChar(t[1..|t|-1], c) + (if t[|t|-1]==c then 1 else 0)
        assert CountChar(t, c) == (if t[0] == c then 1 else 0) + CountChar(t[1..|t|-1], c) + (if t[|t|-1] == c then 1 else 0);
        // Also unfold CountChar for the prefix t[..|t|-1]
        assert CountChar(t[..|t|-1], c) == (if t[0] == c then 1 else 0) + CountChar(t[1..|t|-1], c);
        // Combine
        assert CountChar(t, c) == CountChar(t[..|t|-1], c) + (if t[|t|-1] == c then 1 else 0);
    }
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
      plus := plus + 1;
      // update relation for '+' prefix
      CountChar_last(s[..i+1], '+');
      // plus now equals CountChar(s[..i+1], '+')
      assert plus == CountChar(s[..i+1], '+');
      // for '-' the last char is '+', so CountChar(s[..i+1], '-') == CountChar(s[..i], '-')
      CountChar_last(s[..i+1], '-');
      assert (if s[i] == '-' then 1 else 0) == 0;
      assert minus == CountChar(s[..i+1], '-');
    } else {
      // ch must be '-'
      minus := minus + 1;
      CountChar_last(s[..i+1], '-');
      assert minus == CountChar(s[..i+1], '-');
      CountChar_last(s[..i+1], '+');
      assert (if s[i] == '+' then 1 else 0) == 0;
      assert plus == CountChar(s[..i+1], '+');
    }
    i := i + 1;
  }
  result := plus - minus;
}
// </vc-code>

