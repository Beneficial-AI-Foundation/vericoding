// <vc-preamble>
const P: int := 1000000007

predicate ValidInput(input: string)
{
    |input| > 0 &&
    (exists spaceIndex :: 0 <= spaceIndex < |input| && input[spaceIndex] == ' ') &&
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpace(trimmed);
    |parts| >= 2 && 
    StringToInt(parts[0]) >= 1 && 
    StringToInt(parts[1]) >= 1 &&
    StringToInt(parts[0]) <= 1000000 &&
    StringToInt(parts[1]) <= 1000000
}

function GetN(input: string): int
    requires ValidInput(input)
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpace(trimmed);
    StringToInt(parts[0])
}

function GetM(input: string): int
    requires ValidInput(input)
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpace(trimmed);
    StringToInt(parts[1])
}

function ExpectedResult(n: int, m: int): int
    requires n >= 1 && m >= 1
{
    if m == 1 then n + 1
    else 
        var term1 := (m * power(2 * m - 1, n, P)) % P;
        var term2 := power(m, n, P);
        var numerator := (term1 - term2 + P) % P;
        var inv := power(m - 1, P - 2, P);
        (numerator * inv) % P
}
// </vc-preamble>

// <vc-helpers>
function power(base: int, exp: int, mod: int): int
    requires exp >= 0
    requires mod > 0
    decreases exp
{
    if exp == 0 then 1
    else if exp % 2 == 0 then
        var half := power(base, exp / 2, mod);
        (half * half) % mod
    else
        (base * power(base, exp - 1, mod)) % mod
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then -StringToIntHelper(s[1..])
    else StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then s[0] as int - '0' as int
    else 10 * StringToIntHelper(s[..|s|-1]) + (s[|s|-1] as int - '0' as int)
}

function SplitOnSpace(s: string): seq<string>
{
    if |s| == 0 then []
    else
        var spaceIndex := FindSpace(s, 0);
        if spaceIndex == -1 then [s]
        else [s[..spaceIndex]] + SplitOnSpace(s[spaceIndex+1..])
}

function FindSpace(s: string, start: int): int
    requires 0 <= start
    ensures (FindSpace(s, start) == -1) || (0 <= FindSpace(s, start) < |s|)
    decreases |s| - start
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else FindSpace(s, start + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: int)
    requires ValidInput(input)
    ensures result >= 0
    ensures result < P
    ensures result == ExpectedResult(GetN(input), GetM(input))
// </vc-spec>
// <vc-code>
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpace(trimmed);
    var n := StringToInt(parts[0]);
    var k := StringToInt(parts[1]);

    if k == 1 {
        result := n + 1;
    } else {
        var term1 := (k * power(2 * k - 1, n, P)) % P;
        var term2 := power(k, n, P);
        var numerator := (term1 - term2 + P) % P;
        var inv := power(k - 1, P - 2, P);
        result := (numerator * inv) % P;
    }
}
// </vc-code>
