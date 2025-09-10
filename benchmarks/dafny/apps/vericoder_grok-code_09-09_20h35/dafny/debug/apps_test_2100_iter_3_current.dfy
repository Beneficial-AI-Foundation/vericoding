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
function method Split(s: seq<char>, d: char): seq<seq<char>>
    ensures |result| > 0 <==> |s| > 0
{
    if |s| == 0 {
        result := [];
    } else {
        var pos := FindPos(d, s);
        if pos == |s| {
            result := [s];
        } else {
            result := [s[..pos]] + Split(s[pos+1..], d);
        }
    }
}

function method FindPos(d: char, s: seq<char>): int
    decreases |s|
    ensures 0 <= result <= |s|
{
    if |s| == 0 {
        result := 0;
    } else if s[0] == d {
        result := 0;
    } else {
        result := 1 + FindPos(d, s[1..]);
    }
}

function method StringToInt(s: seq<char>): int
    requires IsValidNumber(s)
{
    result := StringToIntAcc(s, 0);
}

function method StringToIntAcc(s: seq<char>, acc: int): int
    requires |s| == 0 || IsValidNumber(s)
    decreases |s|
{
    if |s| == 0 {
        result := acc;
    } else {
        result := StringToIntAcc(s[1..], acc * 10 + (s[0] as int - '0' as int));
    }
}

function method IntToString(n: int): seq<char>
    requires n >= 0
{
    if n == 0 {
        result := "0";
    } else {
        result := ToString(n, []);
    }
}

function method ToString(n: int, acc: seq<char>): seq<char>
    requires n >= 0
    decreases n
{
    if n == 0 {
        result := acc;
    } else {
        result := ToString(n / 10, [(n % 10 + '0' as int) as char] + acc);
    }
}

function method CountLeftZeros(lines: seq<seq<char>>, start: int, n: int): int
    requires 0 <= start <= n + 1
    decreases n - start
{
    if start > n {
        result := 0;
    } else {
        result := (if Split(lines[start], ' ')[0] == "0" then 1 else 0) + CountLeftZeros(lines, start + 1, n);
    }
}

function method CountRightZeros(lines: seq<seq<char>>, start: int, n: int): int
    requires 0 <= start <= n + 1
    decreases n - start
{
    if start > n {
        result := 0;
    } else {
        result := (if Split(lines[start], ' ')[1] == "0" then 1 else 0) + CountRightZeros(lines, start + 1, n);
    }
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

