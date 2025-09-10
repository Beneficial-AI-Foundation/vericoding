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
function MaxDivisibleBy3SegmentsHelper(s: string, start: int, current: string, maxCount: int): int
    requires 0 <= start <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires forall i :: 0 <= i < |current| ==> '0' <= current[i] <= '9'
    requires maxCount >= 0
    ensures MaxDivisibleBy3SegmentsHelper(s, start, current, maxCount) >= 0
    decreases |s| - start
{
    if start == |s| then
        if |current| > 0 && IsDivisibleBy3(current) then maxCount + 1 else maxCount
    else
        var withCurrent := MaxDivisibleBy3SegmentsHelper(s, start + 1, current + [s[start]], maxCount);
        var withoutCurrent := if |current| > 0 && IsDivisibleBy3(current) 
                             then MaxDivisibleBy3SegmentsHelper(s, start + 1, [s[start]], maxCount + 1)
                             else MaxDivisibleBy3SegmentsHelper(s, start + 1, [s[start]], maxCount);
        if withCurrent >= withoutCurrent then withCurrent else withoutCurrent
}

predicate IsDivisibleBy3(s: string)
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    |s| > 0 && SumOfDigits(s) % 3 == 0
}

function SumOfDigits(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures SumOfDigits(s) >= 0
{
    if |s| == 0 then 0
    else (s[0] as int - '0' as int) + SumOfDigits(s[1..])
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| > 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
{
    if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + n % 10) as char]
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
    var inputDigits := input[0..|input|-1];
    var count := MaxDivisibleBy3Segments(inputDigits);
    var countStr := IntToString(count);
    result := countStr + "\n";
}
// </vc-code>

