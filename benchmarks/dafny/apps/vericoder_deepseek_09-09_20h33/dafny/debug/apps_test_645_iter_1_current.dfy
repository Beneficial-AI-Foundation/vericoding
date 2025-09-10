predicate IsVowel(c: char) {
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

predicate IsOddDigit(c: char) {
  c == '1' || c == '3' || c == '5' || c == '7' || c == '9'
}

predicate NeedsFlipping(c: char) {
  IsVowel(c) || IsOddDigit(c)
}

function CountFlips(s: string): int {
  |set i | 0 <= i < |s| && NeedsFlipping(s[i])|
}

// <vc-helpers>
lemma DigitToIntLemma(c: char)
  requires '0' <= c <= '9'
  ensures (c - '0') as int >= 0 && (c - '0') as int <= 9
{
}

lemma DigitOddLemma(c: char)
  requires IsOddDigit(c)
  ensures (c - '0') as int % 2 == 1
{
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
  requires |s| >= 1 && |s| <= 50
  ensures |result| > 0
  ensures result == toString(CountFlips(s)) + "\n"
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == |set j | 0 <= j < i && NeedsFlipping(s[j])|
  {
    if NeedsFlipping(s[i]) {
      count := count + 1;
    }
    i := i + 1;
  }
  
  result := count.ToString() + "\n";
}
// </vc-code>

