predicate ValidInput(input: string)
{
    |input| > 0 &&
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpace(trimmed);
    |parts| >= 1
}

function GetExpectedResult(input: string): string
    requires ValidInput(input)
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpace(trimmed);
    if parts[|parts|-1] == "month" then
        if parts[0] == "31" then "7\n"
        else if parts[0] == "30" then "11\n"
        else "12\n"
    else
        if parts[0] == "5" || parts[0] == "6" then "53\n"
        else "52\n"
}

// <vc-helpers>
function SplitOnSpace(s: string): seq<string>
{
    SplitOnSpaceHelper(s, 0, 0, [])
}

function SplitOnSpaceHelper(s: string, start: nat, i: nat, acc: seq<string>): seq<string>
    requires start <= i <= |s|
    decreases |s| - i
{
    if i == |s| then
        if start == i then acc
        else acc + [s[start..i]]
    else if s[i] == ' ' then
        if start == i then
            SplitOnSpaceHelper(s, i + 1, i + 1, acc)
        else
            SplitOnSpaceHelper(s, i + 1, i + 1, acc + [s[start..i]])
    else
        SplitOnSpaceHelper(s, start, i + 1, acc)
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == GetExpectedResult(input)
// </vc-spec>
// <vc-code>
{
    var trimmed := if |input| > 0 && input[|input|-1] == '\n' then input[..|input|-1] else input;
    var parts := SplitOnSpace(trimmed);
    
    if parts[|parts|-1] == "month" {
        if parts[0] == "31" {
            result := "7\n";
        } else if parts[0] == "30" {
            result := "11\n";
        } else {
            result := "12\n";
        }
    } else {
        if parts[0] == "5" || parts[0] == "6" {
            result := "53\n";
        } else {
            result := "52\n";
        }
    }
}
// </vc-code>

