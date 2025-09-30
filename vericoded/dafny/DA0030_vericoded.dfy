predicate IsValidInput(input: string)
{
    var lines := SplitLines(input);
    |lines| >= 3 && 
    ParseInt(lines[0]) > 0 &&
    |ParseIntArray(lines[1])| == ParseInt(lines[0]) &&
    |ParseIntArray(lines[2])| == ParseInt(lines[0])
}

function GetInitialSum(input: string): int
    requires IsValidInput(input)
{
    var lines := SplitLines(input);
    Sum(ParseIntArray(lines[1]))
}

function GetTargetSum(input: string): int
    requires IsValidInput(input)
{
    var lines := SplitLines(input);
    Sum(ParseIntArray(lines[2]))
}

function Sum(nums: seq<int>): int
    decreases |nums|
{
    if |nums| == 0 then 0
    else nums[0] + Sum(nums[1..])
}

// <vc-helpers>
function SplitLines(input: string): seq<string>
{
    SplitLinesHelper(input, 0, 0)
}

function SplitLinesHelper(input: string, start: nat, pos: nat): seq<string>
    requires start <= pos <= |input|
    decreases |input| - pos
{
    if pos == |input| then
        if start == pos then []
        else [input[start..pos]]
    else if input[pos] == '\n' then
        [input[start..pos]] + SplitLinesHelper(input, pos + 1, pos + 1)
    else
        SplitLinesHelper(input, start, pos + 1)
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' && |s| > 1 then -(ParseNat(s[1..]) as int)
    else ParseNat(s)
}

function ParseNat(s: string): nat
{
    if |s| == 0 then 0
    else if IsDigit(s[0]) then
        (s[0] as int - '0' as int) * Power10(|s| - 1) + ParseNat(s[1..])
    else 0
}

function Power10(n: nat): nat
{
    if n == 0 then 1
    else 10 * Power10(n - 1)
}

predicate IsDigit(c: char)
{
    '0' <= c <= '9'
}

function ParseIntArray(s: string): seq<int>
{
    ParseIntArrayHelper(s, 0, 0)
}

function ParseIntArrayHelper(s: string, start: nat, pos: nat): seq<int>
    requires start <= pos <= |s|
    decreases |s| - pos
{
    if pos == |s| then
        if start == pos then []
        else [ParseInt(s[start..pos])]
    else if s[pos] == ' ' then
        if start == pos then ParseIntArrayHelper(s, pos + 1, pos + 1)
        else [ParseInt(s[start..pos])] + ParseIntArrayHelper(s, pos + 1, pos + 1)
    else
        ParseIntArrayHelper(s, start, pos + 1)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    ensures result == "Yes" || result == "No"
    ensures IsValidInput(input) ==> 
        (result == "Yes" <==> GetInitialSum(input) >= GetTargetSum(input))
    ensures !IsValidInput(input) ==> result == "No"
// </vc-spec>
// <vc-code>
{
    if !IsValidInput(input) {
        return "No";
    }
    
    var lines := SplitLines(input);
    var initialSum := Sum(ParseIntArray(lines[1]));
    var targetSum := Sum(ParseIntArray(lines[2]));
    
    if initialSum >= targetSum {
        result := "Yes";
    } else {
        result := "No";
    }
}
// </vc-code>

