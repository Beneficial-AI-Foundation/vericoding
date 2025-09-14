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
function findSpace(input: string): int
    requires exists spacePos :: 0 < spacePos < |input| - 1 && input[spacePos] == ' ' &&
                  (forall i :: 0 <= i < spacePos ==> input[i] != ' ') &&
                  (forall i :: spacePos + 1 <= i < |input| ==> input[i] != ' ')
    ensures input[findSpace(input)] == ' ' && 0 < findSpace(input) < |input| - 1
    decreases |input|
{
    if |input| == 0 then 0
    else if input[0] == ' ' then 0
    else findSpace(input[1..]) + 1
}

function isValidInteger(s: string): bool
{
    if |s| == 0 then
        false
    else if s[0] == '-' then
        |s| > 1 && (forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9')
    else
        (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function parseInt(s: string): int
    requires isValidInteger(s)
{
    if s[0] == '-' then
        -parseIntPositive(s[1..])
    else
        parseIntPositive(s)
}

function parseIntPositive(s: string): int
    requires |s| > 0 && (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
    decreases |s|
{
    if |s| == 1 then
        (s[0] as int) - ('0' as int)
    else
        10 * parseIntPositive(s[..|s|-1]) + ((s[|s|-1] as int) - ('0' as int))
}

function intToString(n: int): string
{
  if n < 0 then
      "-" + intToStringPositive(-n)
  else
      intToStringPositive(n)
}

function intToStringPositive(n: int): string
    requires n >= 0
    decreases n
{
    if n < 10 then
        [charForDigit(n)]
    else
        intToStringPositive(n / 10) + [charForDigit(n % 10)]
}

function charForDigit(n: int): char
    requires 0 <= n <= 9
{
    '0' + n
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
    var maxVal := max3(a + b, a - b, a * b);
    return intToString(maxVal) + "\n";
}
// </vc-code>

