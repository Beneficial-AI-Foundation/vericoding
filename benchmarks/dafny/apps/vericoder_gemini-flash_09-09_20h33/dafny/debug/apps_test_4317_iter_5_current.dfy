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
function findSpace(s: string): (index: int)
    requires exists i :: 0 < i < |s| && s[i] == ' '
    ensures 0 < index < |s|
    ensures s[index] == ' '
    ensures forall i' :: 0 <= i' < index ==> s[i'] != ' '
{
    var i := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant forall j :: 0 <= j < i ==> s[j] != ' '
    {
        if s[i] == ' ' then return i;
        i := i + 1;
    }
    // This should be unreachable given the precondition
    -1 // Dummy return
}

function isValidInteger(s: string): bool
{
    |s| > 0 &&
    (s[0] == '-' ==> |s| > 1 && (forall i :: 1 <= i < |s| ==> '0' <= s[i] <= '9')) &&
    (s[0] != '-' ==> (forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'))
}

function parseInt(s: string): int
    requires isValidInteger(s)
    reads s
    ensures -200_000 <= parseInt(s) <= 200_000 // A reasonable bound for given constraints
{
    var res := 0;
    var sign := 1;
    var i := 0;

    if s[0] == '-' {
        sign := -1;
        i := 1;
    }

    while i < |s|
        invariant 0 <= i <= |s|
        invariant (sign == 1 && 0 <= res) || (sign == -1 && 0 <= -res)
        invariant forall j :: (if sign == -1 then 1 else 0) <= j < i ==> '0' <= s[j] <= '9'
    {
        res := res * 10 + (s[i] - '0');
        i := i + 1;
    }
    sign * res
}

function intToString(n: int): string
    ensures (n == 0 ==> intToString(n) == "0")
    ensures (n > 0 ==> forall i :: 0 <= i < |intToString(n)| ==> ('0' <= intToString(n)[i] <= '9'))
    ensures (n < 0 ==> intToString(n)[0] == '-')
    ensures (n < 0 ==> forall i :: 1 <= i < |intToString(n)| ==> ('0' <= intToString(n)[i] <= '9'))
    ensures (n > 0 && n < 10 ==> intToString(n) == char(n + '0'))
    ensures (n < 0 && n > -10 ==> intToString(n) == "-" + char(-n + '0'))
{
    if n == 0 then "0"
    else if n < 0 then "-" + intToString(-n)
    else
    (
        var s := "";
        var temp := n;
        while temp > 0
            invariant temp >= 0
            invariant forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
        {
            s := (char(temp % 10 + '0')) + s;
            temp := temp / 10;
        }
        s
    )
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

