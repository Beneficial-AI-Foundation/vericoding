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
function toString(n: int): string {
  if n == 0 then "0"
  else if n < 0 then "-" + toStringAux(-n)
  else toStringAux(n)
}

function toStringAux(n: int): string
  requires n > 0 {
  if n < 10 then DigitToString(n)
  else toStringAux(n / 10) + DigitToString(n % 10)
}

function DigitToString(d: int): string
  requires 0 <= d <= 9 {
  match d
  case 0 => "0"
  case 1 => "1"
  case 2 => "2"
  case 3 => "3"
  case 4 => "4"
  case 5 => "5"
  case 6 => "6"
  case 7 => "7"
  case 8 => "8"
  case 9 => "9"
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
  result := toString(CountFlips(s)) + "\n";
}
// </vc-code>

