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
function SplitOnSpaces(s: string): seq<string>
    ensures |SplitOnSpaces(s)| >= 1
{
    if |s| == 0 then [""]
    else if s[0] == ' ' then SplitOnSpaces(s[1..])
    else 
        var i := FindNextSpace(s, 0);
        if i == |s| then [s]
        else [s[..i]] + SplitOnSpaces(s[i+1..])
}

function FindNextSpace(s: string, start: int): int
    requires 0 <= start <= |s|
    ensures start <= FindNextSpace(s, start) <= |s|
    ensures FindNextSpace(s, start) == |s| || s[FindNextSpace(s, start)] == ' '
{
    if start >= |s| then |s|
    else if s[start] == ' ' then start
    else FindNextSpace(s, start + 1)
}

function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    StringToIntHelper(s, 0)
}

function StringToIntHelper(s: string, acc: int): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures StringToIntHelper(s, acc) >= acc
{
    if |s| == 0 then acc
    else StringToIntHelper(s[1..], acc * 10 + (s[0] as int - '0' as int))
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| > 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
{
    if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + (n % 10)) as char]
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
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var c := StringToInt(parts[2]);
    var remaining := RemainingWater(a, b, c);
    result := IntToString(remaining) + "\n";
}
// </vc-code>

