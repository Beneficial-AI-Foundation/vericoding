predicate ValidInput(a: int, b: int, c: int)
{
    1 <= b <= a <= 20 && 1 <= c <= 20
}

function RemainingWater(a: int, b: int, c: int): int
    requires ValidInput(a, b, c)
{
    var availableSpace := a - b;
    var remaining := c - availableSpace;
    if remaining >= 0 then remaining else 0
}

// <vc-helpers>
function DropSpaces(s: string): string
  decreases |s|
{
  if |s| == 0 then s
  else if s[0] == ' ' then DropSpaces(s[1..])
  else s
}

function FirstSpaceIndex(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else if s[0] == ' ' then 0
  else 1 + FirstSpaceIndex(s[1..])
}

function SplitOnSpaces(s: string): seq<string>
  decreases |DropSpaces(s)|
{
  if |DropSpaces(s)| == 0 then []
  else if FirstSpaceIndex(DropSpaces(s)) == |DropSpaces(s)| then [DropSpaces(s)]
  else
    [ DropSpaces(s)[..FirstSpaceIndex(DropSpaces(s))] ] +
    SplitOnSpaces(DropSpaces(s)[FirstSpaceIndex(DropSpaces(s)) + 1..])
}

function DigVal(c: char): int
{
  if c == '0' then 0
  else if c == '1' then 1
  else if c == '2' then 2
  else if c == '3' then 3
  else if c == '4' then 4
  else if c == '5' then 5
  else if c == '6' then 6
  else if c == '7' then 7
  else if c == '8' then 8
  else if c == '9' then 9
  else 0
}

function StringToInt(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else 10 * StringToInt(s[..|s|-1]) + DigVal(s[|s|-1])
}

function DigitChar(n: int): char
  requires 0 <= n < 10
{
  if n == 0 then '0'
  else if n == 1 then '1'
  else if n == 2 then '2'
  else if n == 3 then '3'
  else if n == 4 then '4'
  else if n == 5 then '5'
  else if n == 6 then '6'
  else if n == 7 then '7'
  else if n == 8 then '8'
  else '9'
}

function IntToStringNonNeg(n: int): string
  requires 0 <= n
  decreases n
{
  if n < 10 then [DigitChar(n)]
  else IntToStringNonNeg(n / 10) + [DigitChar(n % 10)]
}

function IntToString(n: int): string
{
  if n < 0 then "-" + IntToStringNonNeg(-n) else IntToStringNonNeg(n)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             (forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9') &&
             (forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9') &&
             (forall i :: 0 <= i < |parts[2]| ==> '0' <= parts[2][i] <= '9') &&
             |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0
    requires var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
             var parts := SplitOnSpaces(trimmed);
             |parts| == 3 ==>
             ValidInput(StringToInt(parts[0]), StringToInt(parts[1]), StringToInt(parts[2]))
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
            var parts := SplitOnSpaces(trimmed);
            var a := StringToInt(parts[0]);
            var b := StringToInt(parts[1]);
            var c := StringToInt(parts[2]);
            result == IntToString(RemainingWater(a, b, c)) + "\n"
// </vc-spec>
// <vc-code>
{
  var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
  var parts := SplitOnSpaces(trimmed);
  assert |parts| == 3;
  var a := StringToInt(parts[0]);
  var b := StringToInt(parts[1]);
  var c := StringToInt(parts[2]);
  var ans := RemainingWater(a, b, c);
  result := IntToString(ans) + "\n";
}
// </vc-code>

