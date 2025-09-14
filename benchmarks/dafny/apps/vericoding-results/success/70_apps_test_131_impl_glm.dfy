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
function IndexOf(s: string, c: char): int
    decreases |s|
    ensures -1 <= IndexOf(s, c) < |s|
{
    if |s| == 0 then -1
    else if s[0] == c then 0
    else 
        var rec := IndexOf(s[1..], c);
        if rec < 0 then -1 else rec + 1
}

function Split(s: string, delimiter: char): seq<string>
    decreases |s|
{
    if s == "" then []
    else 
        var index := IndexOf(s, delimiter);
        if index < 0 then [s]
        else [s[..index]] + Split(s[index+1..], delimiter)
}

function SplitLines(s: string): seq<string>
{
    Split(s, '\n')
}

function CharToInt(c: char): int
    requires '0' <= c <= '9'
{
    if c == '0' then 0
    else if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else 9
}

function ParseInt(s: string): int
    decreases |s|
{
    if |s| == 0 then 0
    else if s[0] < '0' || s[0] > '9' then ParseInt(s[1..])
    else CharToInt(s[0]) + 10 * ParseInt(s[1..])
}

function ParseIntArray(s: string): seq<int>
{
    var tokens := Split(s, ' ');
    seq(|tokens|, i requires 0 <= i < |tokens| => ParseInt(tokens[i]))
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
    if IsValidInput(input) {
        if GetInitialSum(input) >= GetTargetSum(input) {
            return "Yes";
        } else {
            return "No";
        }
    } else {
        return "No";
    }
}
// </vc-code>

