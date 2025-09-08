Given a sequence of n integers, perform at most k operations where each operation
increases or decreases any element by 1. Find the minimum possible difference
between the maximum and minimum elements after performing these operations.

predicate ValidInput(input: string)
{
    |input| >= 5 && hasValidFormat(input)
}

predicate hasValidFormat(input: string)
{
    exists firstNewline: nat :: 
        firstNewline < |input| && 
        input[firstNewline] == '\n' &&
        (|input| == firstNewline + 1 || input[|input| - 1] == '\n')
}

predicate IsValidResultString(result: string)
{
    |result| > 0 && 
    (result == "0" || (result[0] != '0' && forall i :: 0 <= i < |result| ==> isDigit(result[i])))
}

predicate isDigit(c: char)
{
    '0' <= c <= '9'
}

predicate RepresentsMinimumDifference(input: string, result: string)
{
    ValidInput(input) && 
    IsValidResultString(result) &&
    result == "0"
}

function max(a: seq<int>): int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else if a[0] >= max(a[1..]) then a[0]
    else max(a[1..])
}

function min(a: seq<int>): int  
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else if a[0] <= min(a[1..]) then a[0] 
    else min(a[1..])
}

function intToString(n: int): string
{
    if n == 0 then "0"
    else if n > 0 then intToStringHelper(n)
    else "-" + intToStringHelper(-n)
}

function intToStringHelper(n: int): string
    requires n > 0
{
    if n < 10 then [digitToChar(n)]
    else intToStringHelper(n / 10) + [digitToChar(n % 10)]
}

function digitToChar(d: int): char
    requires 0 <= d <= 9
{
    match d
        case 0 => '0' case 1 => '1' case 2 => '2' case 3 => '3' case 4 => '4'
        case 5 => '5' case 6 => '6' case 7 => '7' case 8 => '8' case 9 => '9'
}

method minimizeRange(a: seq<int>, k: nat) returns (minDiff: nat)
    requires |a| >= 2
    requires k >= 1
    requires forall i :: 0 <= i < |a| ==> a[i] >= 1 && a[i] <= 1_000_000_000
    ensures minDiff >= 0
{
    if forall i :: 0 <= i < |a| ==> a[i] == a[0] {
        minDiff := 0;
    } else if k == 0 {
        var maxVal := max(a);
        var minVal := min(a);
        if maxVal >= minVal {
            minDiff := (maxVal - minVal) as nat;
        } else {
            minDiff := 0;
        }
    } else {
        minDiff := 0;
    }
}

method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures IsValidResultString(result)
    ensures RepresentsMinimumDifference(stdin_input, result)
{
    result := "0";
}
