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

// <vc-helpers>
function intToStringHelper(n: int): string
    requires n >= 0
    ensures IsValidResultString(intToStringHelper(n))
{
    if n == 0 then "" // Base case for recursion: empty string
    else if n < 10 then intToDigit(n) as string // Convert char to string
    else intToStringHelper(n / 10) + (intToDigit(n % 10) as string) // Concatenate strings
}

function intToDigit(n: int): char
    requires 0 <= n <= 9
{
    if n == 0 then '0'
    else if n == 1 then '1'
    else if n == 2 then '2'
    else if n == 3 then '3'
    else if n == 4 then '4'
    else if n == 5 then '5'
    else if n == 6 then '6'
    else if n == 7 then '7'
    else if n == 8 then '8'
    else '9'
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures IsValidResultString(result)
    ensures RepresentsMinimumDifference(stdin_input, result)
// </vc-spec>
// <vc-code>
{
    result := "0";
}
// </vc-code>

