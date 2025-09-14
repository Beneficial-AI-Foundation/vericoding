function Max3(a: int, b: int, c: int): int
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function CalculateMissedMeals(input: string): int
{
    var parts := SplitSpaces(TrimNewline(input));
    if |parts| >= 3 then
        var a := StringToInt(parts[0]);
        var b := StringToInt(parts[1]);  
        var c := StringToInt(parts[2]);
        var maxVal := Max3(a, b, c);
        var threshold := maxVal - 1;
        (if a < threshold then threshold - a else 0) +
        (if b < threshold then threshold - b else 0) +
        (if c < threshold then threshold - c else 0)
    else 0
}

predicate ValidInput(input: string)
{
    |input| > 0
}

// <vc-helpers>
function IsSpace(c: char): bool
{
  c == ' '
}

function TrimNewline(s: string): string
  decreases |s|
{
  if |s| > 0 && (s[|s|-1] == '\n' || s[|s|-1] == '\r') then
    TrimNewline(s[..|s|-1])
  else
    s
}

function DropWhileSpaces(s: string): string
  ensures |DropWhileSpaces(s)| <= |s|
  ensures DropWhileSpaces(s) == s || |DropWhileSpaces(s)| < |s|
  ensures |s| == 0 || !IsSpace(s[0]) ==> DropWhileSpaces(s) == s
  decreases |s|
{
  if |s| > 0 && IsSpace(s[0]) then
    DropWhileSpaces(s[1..])
  else
    s
}

function TokenLen(s: string): nat
  ensures TokenLen(s) <= |s|
  ensures (|s| > 0 && !IsSpace(s[0])) ==> TokenLen(s) >= 1
  decreases |s|
{
  if |s| > 0 && !IsSpace(s[0]) then
    1 + TokenLen(s[1..])
  else
    0
}

function SplitSpaces(s: string): seq<string>
  decreases |s|
{
  var t := DropWhileSpaces(s);
  if |t| == 0 then
    []
  else
    var k := TokenLen(t);
    var tok := t[..k];
    var rest := t[k..];
    [tok] + SplitSpaces(rest)
}

function IsDigit(ch: char): bool
{
  '0' <= ch && ch <= '9'
}

function DigitVal(ch: char): int
  requires IsDigit(ch)
{
  if ch == '0' then 0
  else if ch == '1' then 1
  else if ch == '2' then 2
  else if ch == '3' then 3
  else if ch == '4' then 4
  else if ch == '5' then 5
  else if ch == '6' then 6
  else if ch == '7' then 7
  else if ch == '8' then 8
  else 9
}

function ParseUnsignedRec(s: string, acc: int): int
  decreases |s|
{
  if |s| == 0 then acc
  else if IsDigit(s[0]) then
    ParseUnsignedRec(s[1..], acc * 10 + DigitVal(s[0]))
  else
    acc
}

function StringToInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then
    -ParseUnsignedRec(s[1..], 0)
  else
    ParseUnsignedRec(s, 0)
}

function DigitString(d: int): string
  requires 0 <= d < 10
{
  if d == 0 then "0"
  else if d == 1 then "1"
  else if d == 2 then "2"
  else if d == 3 then "3"
  else if d == 4 then "4"
  else if d == 5 then "5"
  else if d == 6 then "6"
  else if d == 7 then "7"
  else if d == 8 then "8"
  else "9"
}

function UnsignedToString(n: int): string
  requires 0 <= n
  decreases n
{
  if n < 10 then
    DigitString(n)
  else
    UnsignedToString(n / 10) + DigitString(n % 10)
}

function IntToString(n: int): string
{
  if n < 0 then "-" + UnsignedToString(-n) else UnsignedToString(n)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures result == IntToString(CalculateMissedMeals(input))
// </vc-spec>
// <vc-code>
{
  result := IntToString(CalculateMissedMeals(input));
}
// </vc-code>

