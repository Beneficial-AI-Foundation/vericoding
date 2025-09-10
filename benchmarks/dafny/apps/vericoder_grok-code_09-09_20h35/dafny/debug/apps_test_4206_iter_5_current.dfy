predicate ValidInput(input: string)
{
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    |input| >= 2 &&
    (forall i :: 0 <= i < |input|-1 ==> '0' <= input[i] <= '9') &&
    (input[0] != '0' || |input| == 2)
}

function MaxDivisibleBy3Segments(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures MaxDivisibleBy3Segments(s) >= 0
    ensures MaxDivisibleBy3Segments(s) <= |s|
{
    MaxDivisibleBy3SegmentsHelper(s, 0, "", 0)
}

// <vc-helpers>
function SumMod3(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 0 then 0
    else {
        var digit := (s[|s|-1] as int) - ('0' as int);
        ((digit % 3) + SumMod3(s[0..|s|-1])) % 3
    }
}

function MaxDivisibleBy3Segments(s: string): int
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures MaxDivisibleBy3Segments(s) >= 0
    ensures MaxDivisibleBy3Segments(s) <= |s|
    decreases |s|
{
    if SumMod3(s) == 0 then |s|
    else if |s| == 1 then 0
    else MaxDivisibleBy3Segments(s[0..|s|-1])
}

function IntToString(n: int): string
    requires n >= 0
    decreases n
{
    if n == 0 then "0"
    else if n < 10 then [char(('0' as int) + n % 10)]
    else IntToString(n / 10) + [char(('0' as int) + n % 10)]
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists count :: 0 <= count <= |input|-1 && result == IntToString(count) + "\n"
    ensures exists count :: count == MaxDivisibleBy3Segments(input[0..|input|-1]) && result == IntToString(count) + "\n"
// </vc-spec>
// <vc-code>
{
    var s := input[0..|input|-1];
    var count := MaxDivisibleBy3Segments(s);
    result := IntToString(count) + "\n";
}
// </vc-code>

