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
    ensures |SplitOnSpace(s)| >= 1
    ensures forall i :: 0 <= i < |SplitOnSpace(s)| ==> forall j :: 0 <= j < |SplitOnSpace(s)[i]| ==> SplitOnSpace(s)[i][j] != ' '
{
    if |s| == 0 then [""]
    else if s[0] == ' ' then SplitOnSpace(s[1..])
    else 
        var rest := SplitOnSpace(s[1..]);
        if |s| == 1 then [s]
        else if s[1] == ' ' then [s[..1]] + rest
        else [s[..1] + rest[0]] + rest[1..]
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

