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
function Split(s: seq<char>, d: char): seq<seq<char>>
{
    if |s| == 0 then []
    else
        var pos := FindPos(d, s);
        if pos == |s| then [s]
        else [s[..pos]] + Split(s[pos+1..], d)
}

function FindPos(d: char, s: seq<char>): int
{
    if |s| == 0 then |s|
    else if s[0] == d then 0
    else 1 + FindPos(d, s[1..])
}

function StringToInt(s: seq<char>): int
    requires IsValidNumber(s)
{
    StringToIntAcc(s, 0)
}

function StringToIntAcc(s: seq<char>, acc: int): int
    requires IsValidNumber(s)
    decreases |s|
{
    if |s| == 0 then acc
    else StringToIntAcc(s[1..], acc * 10 + (s[0] as int - '0' as int))
}

function IntToString(n: int): seq<char>
    requires n >= 0
{
    if n == 0 then "0"
    else ToString(n, [])
}

function ToString(n: int, acc: seq<char>): seq<char>
    requires n >= 0
{
    if n == 0 then acc
    else ToString(n / 10, [(n % 10 + '0' as int) as char] + acc)
}

function CountLeftZeros(lines: seq<seq<char>>, start: int, n: int): int
{
    if start > n then 0
    else (if Split(lines[start], ' ')[0] == "0" then 1 else 0) + CountLeftZeros(lines, start + 1, n)
}

function CountRightZeros(lines: seq<seq<char>>, start: int, n: int): int
{
    if start > n then 0
    else (if Split(lines[start], ' ')[1] == "0" then 1 else 0) + CountRightZeros(lines, start + 1, n)
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
    result := CalculateMinOperations(input);
}
// </vc-code>

