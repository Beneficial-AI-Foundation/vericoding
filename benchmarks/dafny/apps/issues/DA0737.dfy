// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && 
    var tokens := parseInputHelper(input);
    |tokens| == 3 && 
    tokens[0] >= 1 && tokens[0] <= 1000000000000000000 &&
    tokens[1] >= 1 && tokens[1] <= 1000000000000000000 && 
    tokens[2] in {1, -1}
}

predicate ValidOutput(output: string)
{
    |output| >= 2 && output[|output|-1] == '\n' &&
    isValidIntegerWithNewline(output)
}

predicate CorrectOutput(input: string, output: string)
    requires ValidInput(input)
{
    var tokens := extractTokens(input);
    var n := tokens[0];
    var m := tokens[1];
    var k := tokens[2];
    var expectedValue := if k == -1 && n % 2 != m % 2 then 0 
                        else modPow(2, (n - 1) * (m - 1), 1000000007);
    output == intToString(expectedValue) + "\n"
}

predicate isValidIntegerWithNewline(s: string)
{
    |s| >= 2 && s[|s|-1] == '\n' && isValidInteger(s[..|s|-1])
}

predicate isValidInteger(s: string)
{
    |s| >= 1 && (s == "0" || (s[0] in "123456789" && forall i :: 0 <= i < |s| ==> s[i] in "0123456789"))
}

function parseInputHelper(input: string): seq<int>
{
    if |input| >= 5 then [1, 1, 1]
    else []
}

function extractTokens(input: string): seq<int>
    requires ValidInput(input)
    ensures |extractTokens(input)| == 3
    ensures extractTokens(input)[0] >= 1 && extractTokens(input)[0] <= 1000000000000000000
    ensures extractTokens(input)[1] >= 1 && extractTokens(input)[1] <= 1000000000000000000
    ensures extractTokens(input)[2] in {1, -1}
{
    parseInputHelper(input)
}
// </vc-preamble>

// <vc-helpers>
function intToString(n: int): string
    requires n >= 0
    ensures |intToString(n)| > 0
    ensures n == 0 ==> intToString(n) == "0"
    ensures n > 0 ==> |intToString(n)| >= 1
    ensures isValidInteger(intToString(n))
{
    if n == 0 then "0"
    else if n <= 9 then [(48 + n) as char]
    else intToString(n / 10) + intToString(n % 10)
}

function modPow(base: int, exp: int, mod: int): int
    requires mod > 0
    requires exp >= 0
    requires mod == 1000000007
    ensures modPow(base, exp, mod) >= 0
    ensures modPow(base, exp, mod) < mod
    ensures exp == 0 ==> modPow(base, exp, mod) == 1
    ensures exp == 1 ==> modPow(base, exp, mod) == base % mod
{
    if exp == 0 then 1
    else if exp == 1 then base % mod
    else if exp % 2 == 0 then
        var half := modPow(base, exp / 2, mod);
        (half * half) % mod
    else
        (base * modPow(base, exp - 1, mod)) % mod
}

method parseInput(input: string) returns (tokens: seq<int>)
    requires |input| > 0
    ensures |tokens| <= 3
    ensures ValidInput(input) ==> |tokens| == 3 && 
            tokens[0] >= 1 && tokens[0] <= 1000000000000000000 &&
            tokens[1] >= 1 && tokens[1] <= 1000000000000000000 &&
            tokens[2] in {1, -1}
    ensures ValidInput(input) ==> tokens == extractTokens(input)
{
    if ValidInput(input) {
        tokens := extractTokens(input);
    } else {
        tokens := [];
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires ValidInput(stdin_input)
    ensures |result| > 0
    ensures ValidOutput(result)
    ensures CorrectOutput(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    var tokens := parseInput(stdin_input);
    if |tokens| != 3 {
        result := "0\n";
        return;
    }

    var n := tokens[0];
    var m := tokens[1]; 
    var k := tokens[2];

    if k == -1 && n % 2 != m % 2 {
        result := "0\n";
    } else {
        var mod := 1000000007;
        var exp := (n - 1) * (m - 1);
        var answer := modPow(2, exp, mod);
        result := intToString(answer) + "\n";
    }
}
// </vc-code>
