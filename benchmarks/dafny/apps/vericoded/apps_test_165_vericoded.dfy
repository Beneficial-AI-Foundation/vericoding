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
function SplitSpaces(s: string): seq<string>
{
    SplitSpacesHelper(s, 0, 0, [])
}

function SplitSpacesHelper(s: string, start: nat, i: nat, acc: seq<string>): seq<string>
    requires start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if start == i then acc
        else acc + [s[start..i]]
    else if s[i] == ' ' then
        if start == i then
            SplitSpacesHelper(s, i + 1, i + 1, acc)
        else
            SplitSpacesHelper(s, i + 1, i + 1, acc + [s[start..i]])
    else
        SplitSpacesHelper(s, start, i + 1, acc)
}

function TrimNewline(s: string): string
{
    if |s| > 0 && s[|s| - 1] == '\n' then s[..|s| - 1]
    else s
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -(StringToNat(s[1..]) as int)
    else StringToNat(s) as int
}

function StringToNat(s: string): nat
{
    if |s| == 0 then 0
    else 
        var digit := if '0' <= s[0] <= '9' then (s[0] as int) - ('0' as int) else 0;
        digit * Power10(|s| - 1) + StringToNat(s[1..])
}

function Power10(n: nat): nat
{
    if n == 0 then 1
    else 10 * Power10(n - 1)
}

function IntToString(n: int): string
{
    if n < 0 then "-" + NatToString(-n)
    else NatToString(n)
}

function NatToString(n: nat): string
{
    if n < 10 then 
        [(n + '0' as int) as char]
    else 
        NatToString(n / 10) + [(n % 10 + '0' as int) as char]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
requires ValidInput(input)
ensures result == IntToString(CalculateMissedMeals(input))
// </vc-spec>
// <vc-code>
{
    var missedMeals := CalculateMissedMeals(input);
    result := IntToString(missedMeals);
}
// </vc-code>

