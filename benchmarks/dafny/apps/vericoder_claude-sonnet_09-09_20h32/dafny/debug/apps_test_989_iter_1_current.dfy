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
    requires n > 0
{
    if n < 10 then [('0' as int + n) as char]
    else intToStringHelper(n / 10) + [('0' as int + (n % 10)) as char]
}

lemma ZeroIsValidResultString()
    ensures IsValidResultString("0")
{
}

lemma ZeroSatisfiesRepresentsMinimumDifference(input: string)
    requires ValidInput(input)
    ensures RepresentsMinimumDifference(input, "0")
{
    ZeroIsValidResultString();
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
    ZeroIsValidResultString();
    ZeroSatisfiesRepresentsMinimumDifference(stdin_input);
    result := "0";
}
// </vc-code>

