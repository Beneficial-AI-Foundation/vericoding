predicate ValidInput(input: string)
{
    |input| >= 3 &&
    exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' ' &&
    (forall i :: 0 <= i < spacePos ==> input[i] != ' ') &&
    (forall i :: spacePos + 1 <= i < |input| ==> input[i] != ' ' || input[i] == '\n') &&
    isValidInteger(getAString(input)) && isValidInteger(getBString(input)) &&
    -100 <= getA(input) <= 100 && -100 <= getB(input) <= 100
}

function getA(input: string): int
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
    requires isValidInteger(getAString(input))
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    parseInt(trimmed[..spaceIndex])
}

function getB(input: string): int
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
    requires isValidInteger(getBString(input))
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    parseInt(trimmed[spaceIndex+1..])
}

function getAString(input: string): string
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    trimmed[..spaceIndex]
}

function getBString(input: string): string
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    trimmed[spaceIndex+1..]
}

function max3(a: int, b: int, c: int): int
    ensures max3(a, b, c) >= a && max3(a, b, c) >= b && max3(a, b, c) >= c
    ensures max3(a, b, c) == a || max3(a, b, c) == b || max3(a, b, c) == c
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

// <vc-helpers>
predicate ValidInput(input: string)
{
    |input| >= 3 &&
    (exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' ' &&
    (forall i :: 0 <= i < spacePos ==> input[i] != ' ') &&
    (forall i :: spacePos + 1 <= i < |input| ==> input[i] != ' ' || input[i] == '\n') &&
    isValidInteger(getAString(input)) && isValidInteger(getBString(input)) &&
    -100 <= getA(input) <= 100 && -100 <= getB(input) <= 100)
}

function getA(input: string): int
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
    requires isValidInteger(getAString(input))
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    parseInt(trimmed[..spaceIndex])
}

function getB(input: string): int
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
    requires isValidInteger(getBString(input))
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    parseInt(trimmed[spaceIndex+1..])
}

function getAString(input: string): string
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    trimmed[..spaceIndex]
}

function getBString(input: string): string
    requires |input| >= 3
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' '
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var spaceIndex := findSpace(trimmed);
    trimmed[spaceIndex+1..]
}

function max3(a: int, b: int, c: int): int
    ensures max3(a, b, c) >= a && max3(a, b, c) >= b && max3(a, b, c) >= c
    ensures max3(a, b, c) == a || max3(a, b, c) == b || max3(a, b, c) == c
{
    if a >= b && a >= c then a
    else if b >= c then b
    else c
}

function digit(c: char): int
  requires '0' <= c <= '9'
  ensures 0 <= digit(c) <= 9
{
  (c as int) - ('0' as int)
}

function isValidInteger(s: string): bool
{
  if |s| == 0 then false
  else if s[0] == '-' then
    1 < |s| && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9'
  else
    forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

function parseNat(s: string, start: int, end: int): int
  requires 0 <= start <= end <= |s|
  requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
  decreases end - start
{
  if start == end then 0
  else parseNat(s, start, end - 1) * 10 + digit(s[end - 1])
}

function parseInt(s: string): int
  requires isValidInteger(s)
{
  if s[0] == '-' then -parseNat(s, 1, |s|)
  else parseNat(s, 0, |s|)
}

function findSpace(s: string): int
  requires exists i :: 0 <= i < |s| && s[i] == ' '
  ensures 0 <= findSpace(s) < |s| && s[findSpace(s)] == ' '
{
  var pos :| 0 <= pos < |s| && s[pos] == ' ';
  pos
}

function intToString(n: int, acc: string := ""): string
  requires -10000 <= n <= 10000
  decreases if n >= 0 then n else -n + 1
{
  if n == 0 then if acc == "" then "0" else acc
  else if n > 0 then intToString(n / 10, [((n % 10 + 48) as char)] + acc)
  else "-" + intToString(-n, acc)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures var maxVal := max3(getA(input) + getB(input), getA(input) - getB(input), getA(input) * getB(input));
            result == intToString(maxVal) + "\n"
    ensures var maxVal := max3(getA(input) + getB(input), getA(input) - getB(input), getA(input) * getB(input));
            -10000 <= maxVal <= 10000
// </vc-spec>
// <vc-code>
{
  var a := getA(input);
  var b := getB(input);
  var opt1 := a + b;
  var opt2 := a - b;
  var opt3 := a * b;
  var maxVal := max3(opt1, opt2, opt3);
  result := intToString(maxVal) + "\n";
}
// </vc-code>

