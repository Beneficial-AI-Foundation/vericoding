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
function toString(n: int): string
  requires n >= 0
{
  if n == 0 then "0"
  else toStringHelper(n)
}

function toStringHelper(n: int): string
  requires n > 0
  decreases n
{
  if n < 10 then
    string([char(n + 48)])
  else
    toStringHelper(n / 10) + string([char(n % 10 + 48)])
}

lemma ToStringLength(n: int)
  requires n >= 0
  ensures |toString(n)| > 0
{
  if n == 0 {
    assert toString(n) == "0";
    assert |toString(n)| == 1;
  } else {
    ToStringHelperLength(n);
  }
}

lemma ToStringHelperLength(n: int)
  requires n > 0
  ensures |toStringHelper(n)| > 0
  decreases n
{
  if n < 10 {
    assert |toStringHelper(n)| == 1;
  } else {
    ToStringHelperLength(n / 10);
    assert |toStringHelper(n / 10)| > 0;
    assert |toStringHelper(n)| == |toStringHelper(n / 10)| + 1;
  }
}

lemma CountFlipsNonNegative(s: string)
  ensures CountFlips(s) >= 0
{
  var flipSet := set i | 0 <= i < |s| && NeedsFlipping(s[i]);
  assert |flipSet| >= 0;
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
  CountFlipsNonNegative(s);
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
  
  ToStringLength(count);
  result := toString(count) + "\n";
}
// </vc-code>

