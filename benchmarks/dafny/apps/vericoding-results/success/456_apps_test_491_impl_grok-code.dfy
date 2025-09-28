predicate ValidInput(n: int)
{
    n >= 10 || n <= -10
}

function MaxBalanceAfterOperation(n: int): int
    requires ValidInput(n)
{
    if n >= 0 then n
    else 
        var s := IntToString(n);
        var option1 := StringToInt(s[..|s|-1]);  // delete last digit
        var option2 := StringToInt(s[..|s|-2] + s[|s|-1..]);  // delete digit before last
        if option1 > option2 then option1 else option2
}

// <vc-helpers>
// IntToString and StringToInt are assumed to be defined or built-in.
// ValidInput ensures |n| >= 10 for negative n, so string length >= 3, avoiding out-of-bounds issues in slicing.
function IntToString(n: int): seq<char> {
  if n == 0 then ['0']
  else if n > 0 then IntToStringDigits(n)
  else ['-'] + IntToStringDigits(-n)
}
function IntToStringDigits(n: nat): seq<char>
  requires n > 0
{
  if n < 10 then [char_from_digit(n)]
  else IntToStringDigits(n / 10) + [char_from_digit(n % 10)]
}
function char_from_digit(d: nat): char
  requires 0 <= d <= 9
{
  if d == 0 then '0' else
  if d == 1 then '1' else
  if d == 2 then '2' else
  if d == 3 then '3' else
  if d == 4 then '4' else
  if d == 5 then '5' else
  if d == 6 then '6' else
  if d == 7 then '7' else
  if d == 8 then '8' else
  if d == 9 then '9' else '0' 
}
function StringToInt(s: seq<char>): int {
  if |s| == 0 then 0
  else if s[0] == '-' then - StringToIntDigits(s[1..])
  else StringToIntDigits(s)
}
function StringToIntDigits(s: seq<char>): int {
  if |s| == 0 then 0
  else StringToIntDigits(s[..|s|-1]) * 10 + digit_value(s[|s|-1])
}
function digit_value(c: char): int {
  if c == '0' then 0 else
  if c == '1' then 1 else
  if c == '2' then 2 else
  if c == '3' then 3 else
  if c == '4' then 4 else
  if c == '5' then 5 else
  if c == '6' then 6 else
  if c == '7' then 7 else
  if c == '8' then 8 else
  if c == '9' then 9 else 0 
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == MaxBalanceAfterOperation(n)
// </vc-spec>
// <vc-code>
{
  if n >= 0 {
    return n;
  } else {
    var s := IntToString(n);
    var option1 := StringToInt(s[..|s|-1]);
    var option2 := StringToInt(s[..|s|-2] + s[|s|-1..]);
    if option1 > option2 {
      return option1;
    } else {
      return option2;
    }
  }
}
// </vc-code>

