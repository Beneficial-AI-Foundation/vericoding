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
function findSpace(s: string): int
    requires |s| >= 3
    requires exists spacePos :: 0 < spacePos < |s| - 1 && s[spacePos] == ' '
    ensures 0 < findSpace(s) < |s| - 1
    ensures s[findSpace(s)] == ' '
    ensures forall i :: 0 <= i < findSpace(s) ==> s[i] != ' '
{
    var spacePos :| 0 < spacePos < |s| - 1 && s[spacePos] == ' ' &&
                    (forall i :: 0 <= i < spacePos ==> s[i] != ' ');
    spacePos
}

predicate isValidInteger(s: string)
{
    |s| > 0 &&
    ((s[0] == '-' && |s| > 1 && forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9') ||
     (s[0] != '-' && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'))
}

function parseInt(s: string): int
    requires isValidInteger(s)
{
    if s[0] == '-' then
        -parseNat(s[1..])
    else
        parseNat(s)
}

function parseNat(s: string): nat
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if |s| == 1 then
        (s[0] - '0') as nat
    else
        parseNat(s[..|s|-1]) * 10 + (s[|s|-1] - '0') as nat
}

function intToString(n: int): string
{
    if n < 0 then
        "-" + natToString((-n) as nat)
    else
        natToString(n as nat)
}

function natToString(n: nat): string
{
    if n < 10 then
        [(n as char + '0')]
    else
        natToString(n / 10) + [(n % 10) as char + '0']
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
    
    var sum := a + b;
    var diff := a - b;
    var prod := a * b;
    
    var maxVal := max3(sum, diff, prod);
    
    result := intToString(maxVal) + "\n";
}
// </vc-code>

