predicate ValidInput(input: string)
{
    var lines := Split(input, '\n');
    |lines| >= 1 &&
    IsValidNumber(lines[0]) &&
    var n := StringToInt(lines[0]);
    n >= 0 && n + 1 <= |lines| &&
    forall i :: 1 <= i <= n && i < |lines| ==>
        var parts := Split(lines[i], ' ');
        |parts| >= 2 && IsValidDoorState(parts[0]) && IsValidDoorState(parts[1])
}

predicate ValidOutput(output: string)
{
    IsValidNumber(output)
}

predicate IsValidNumber(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
}

predicate IsValidDoorState(s: string)
{
    s == "0" || s == "1"
}

function CalculateMinOperations(input: string): string
    requires ValidInput(input)
{
    var lines := Split(input, '\n');
    var n := StringToInt(lines[0]);
    if n == 0 then "0"
    else
        var leftZeros := CountLeftZeros(lines, 1, n);
        var rightZeros := CountRightZeros(lines, 1, n);
        var leftOps := if leftZeros < n - leftZeros then leftZeros else n - leftZeros;
        var rightOps := if rightZeros < n - rightZeros then rightZeros else n - rightZeros;
        IntToString(leftOps + rightOps)
}

// <vc-helpers>
function FindDelimiter(s: string, delimiter: char): nat
    decreases |s|
{
    if s == "" then 0
    else if s[0] == delimiter then 0
    else 1 + FindDelimiter(s[1..], delimiter)
}

function Split(s: string, delimiter: char): seq<string>
    decreases |s|
{
    if s == "" then [""]
    else
        var i := FindDelimiter(s, delimiter);
        if i == |s| then [s]
        else [s[0..i]] + Split(s[i+1..], delimiter)
}

function Power(base: int, exp: nat): int
    decreases exp
{
    if exp == 0 then 1
    else base * Power(base, exp-1)
}

function CharToInt(c: char): int
    requires '0' <= c <= '9'
{
    c - '0'
}

function StringToInt(s: string): int
    requires IsValidNumber(s)
    decreases |s|
{
    if s == "" then 0
    else CharToInt(s[0]) * Power(10, |s|-1) + StringToInt(s[1..])
}

function CharFromDigit(d: int): char
    requires 0 <= d <= 9
{
    '0' + d
}

function IntToString(n: int): string
    requires n >= 0
{
    if n < 10 then [CharFromDigit(n)]
    else IntToString(n / 10) + [CharFromDigit(n % 10)]
}

function CountLeftZeros(lines: seq<string>, start: int, end: int): int
    requires 0 <= start < |lines|
    requires 0 <= end < |lines|
    decreases if start <= end then end - start else 0
{
    if start > end then 0
    else
        var parts := Split(lines[start], ' ');
        (if parts[0] == "0" then 1 else 0) + CountLeftZeros(lines, start+1, end)
}

function CountRightZeros(lines: seq<string>, start: int, end: int): int
    requires 0 <= start < |lines|
    requires 0 <= end < |lines|
    decreases if start <= end then end - start else 0
{
    if start > end then 0
    else
        var parts := Split(lines[start], ' ');
        (if parts[1] == "0" then 1 else 0) + CountRightZeros(lines, start+1, end)
}
// </vc-helpers>

// <vc-spec>
method Solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures |result| > 0
    ensures ValidOutput(result)
    ensures result == CalculateMinOperations(input)
// </vc-spec>
// <vc-code>
{
    var lines := Split(input, '\n');
    var n := StringToInt(lines[0]);
    if n == 0 {
        return "0";
    } else {
        var leftZeros := 0;
        var rightZeros := 0;
        var i := 1;
        while i <= n
            invariant 1 <= i <= n+1
            invariant leftZeros == CountLeftZeros(lines, 1, i-1)
            invariant rightZeros == CountRightZeros(lines, 1, i-1)
        {
            var line := lines[i];
            var parts := Split(line, ' ');
            if parts[0] == "0" {
                leftZeros := leftZeros + 1;
            }
            if parts[1] == "0" {
                rightZeros := rightZeros + 1;
            }
            i := i + 1;
        }
        var leftOps := if leftZeros < n - leftZeros then leftZeros else n - leftZeros;
        var rightOps := if rightZeros < n - rightZeros then rightZeros else n - rightZeros;
        return IntToString(leftOps + rightOps);
    }
}
// </vc-code>

