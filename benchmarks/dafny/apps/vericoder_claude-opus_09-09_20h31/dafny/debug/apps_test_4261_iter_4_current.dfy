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
{
    SplitOnSpacesHelper(s, 0, 0, [])
}

function SplitOnSpacesHelper(s: string, start: nat, i: nat, acc: seq<string>): seq<string>
    requires 0 <= start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if start == i then acc
        else acc + [s[start..i]]
    else if s[i] == ' ' then
        if start == i then
            SplitOnSpacesHelper(s, i + 1, i + 1, acc)
        else
            SplitOnSpacesHelper(s, i + 1, i + 1, acc + [s[start..i]])
    else
        SplitOnSpacesHelper(s, start, i + 1, acc)
}

function StringToInt(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    StringToIntHelper(s, 0, 0)
}

function StringToIntHelper(s: string, i: nat, acc: int): int
    requires 0 <= i <= |s|
    requires forall j :: 0 <= j < |s| ==> '0' <= s[j] <= '9'
    decreases |s| - i
{
    if i == |s| then acc
    else StringToIntHelper(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function DigitToChar(digit: int): char
    requires 0 <= digit <= 9
{
    if digit == 0 then '0'
    else if digit == 1 then '1'
    else if digit == 2 then '2'
    else if digit == 3 then '3'
    else if digit == 4 then '4'
    else if digit == 5 then '5'
    else if digit == 6 then '6'
    else if digit == 7 then '7'
    else if digit == 8 then '8'
    else '9'
}

function IntToString(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else IntToStringHelper(n, [])
}

function IntToStringHelper(n: int, acc: seq<char>): string
    requires n >= 0
    decreases n
{
    if n == 0 then
        if |acc| == 0 then "0"
        else ReverseString(acc)
    else
        var digit := n % 10;
        var ch := DigitToChar(digit);
        IntToStringHelper(n / 10, acc + [ch])
}

function ReverseString(s: seq<char>): string
{
    if |s| == 0 then []
    else ReverseString(s[1..]) + [s[0]]
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
    
    assert |parts| == 3;
    assert |parts[0]| > 0 && |parts[1]| > 0 && |parts[2]| > 0;
    assert forall i :: 0 <= i < |parts[0]| ==> '0' <= parts[0][i] <= '9';
    assert forall i :: 0 <= i < |parts[1]| ==> '0' <= parts[1][i] <= '9';
    assert forall i :: 0 <= i < |parts[2]| ==> '0' <= parts[2][i] <= '9';
    
    var a := StringToInt(parts[0]);
    var b := StringToInt(parts[1]);
    var c := StringToInt(parts[2]);
    
    var remaining := RemainingWater(a, b, c);
    
    result := IntToString(remaining) + "\n";
}
// </vc-code>

