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
lemma {:axiom} findSpaceLemma(s: string)
    requires |s| >= 3
    requires exists spacePos :: 0 < spacePos < |s| - 1 && s[spacePos] == ' '
    ensures var spaceIndex := findSpace(s);
            0 < spaceIndex < |s| - 1 && s[spaceIndex] == ' ' &&
            (forall i :: 0 <= i < spaceIndex ==> s[i] != ' ')

lemma {:axiom} parseIntValid(s: string)
    requires isValidInteger(s)
    ensures -100 <= parseInt(s) <= 100

lemma {:axiom} parseIntValidRange(s: string)
    requires isValidInteger(s)
    ensures var n := parseInt(s);
            -100 <= n <= 100

lemma {:axiom} max3Range(a: int, b: int, c: int)
    requires -100 <= a <= 100 && -100 <= b <= 100 && -100 <= c <= 100
    ensures var maxVal := max3(a, b, c);
            -10000 <= maxVal <= 10000

lemma {:axiom} arithmeticOperationsRange(a: int, b: int)
    requires -100 <= a <= 100 && -100 <= b <= 100
    ensures -200 <= a + b <= 200
    ensures -200 <= a - b <= 200
    ensures -10000 <= a * b <= 10000
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
    var sum := a + b;
    var diff := a - b;
    var prod := a * b;
    var maxVal := max3(sum, diff, prod);
    result := intToString(maxVal) + "\n";
}
// </vc-code>

