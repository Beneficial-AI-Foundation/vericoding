Given two integers A and B, find the maximum value among A + B, A - B, and A × B.
Input constraints: -100 ≤ A, B ≤ 100

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

predicate isValidInteger(s: string)
{
    |s| > 0 &&
    (s[0] == '-' ==> |s| > 1 && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9') &&
    (s[0] != '-' ==> forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9')
}

function findSpace(s: string): int
    requires exists pos :: 0 < pos < |s| && s[pos] == ' '
    ensures 0 < findSpace(s) < |s|
    ensures s[findSpace(s)] == ' '
{
    if s[1] == ' ' then 1
    else 1 + findSpace(s[1..])
}

function parseInt(s: string): int
    requires isValidInteger(s)
{
    if |s| == 0 then 0
    else if s[0] == '-' then -parsePositiveInt(s[1..])
    else parsePositiveInt(s)
}

function parsePositiveInt(s: string): int
    requires |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then charToDigit(s[0])
    else parsePositiveInt(s[..|s|-1]) * 10 + charToDigit(s[|s|-1])
}

function charToDigit(c: char): int
    requires '0' <= c <= '9'
{
    (c as int) - ('0' as int)
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToStringHelper(-n)
    else intToStringHelper(n)
}

function intToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else intToStringHelper(n / 10) + [((n % 10) as char + '0')]
}

method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures var maxVal := max3(getA(input) + getB(input), getA(input) - getB(input), getA(input) * getB(input));
            result == intToString(maxVal) + "\n"
    ensures var maxVal := max3(getA(input) + getB(input), getA(input) - getB(input), getA(input) * getB(input));
            -10000 <= maxVal <= 10000
{
    var trimmed := input;
    if |trimmed| > 0 && trimmed[|trimmed|-1] == '\n' {
        trimmed := trimmed[..|trimmed|-1];
    }

    var spaceIndex := 0;
    while spaceIndex < |trimmed| && trimmed[spaceIndex] != ' ' {
        spaceIndex := spaceIndex + 1;
    }

    var aStr := trimmed[..spaceIndex];
    var bStr := trimmed[spaceIndex+1..];

    var A := parseInt(aStr);
    var B := parseInt(bStr);

    var sum := A + B;
    var diff := A - B;
    var prod := A * B;

    var maxVal := max3(sum, diff, prod);
    result := intToString(maxVal) + "\n";
}
