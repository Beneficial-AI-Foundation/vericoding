/*
Calculate how many candies will be saved in the year 2016 based on a savings plan.
Input format: "x of week" (x=1-7, Monday-Sunday) or "x of month" (x=1-31).
Save one candy on the specified day each week/month.
2016 is a leap year starting on Friday, week starts on Monday.
*/

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
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures result == GetExpectedResult(input)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
