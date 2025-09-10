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
function MaxDivisibleBy3SegmentsHelper(s: string, pos: int, current: string, count: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires forall i :: 0 <= i < |current| ==> '0' <= current[i] <= '9'
    requires count >= 0
    ensures MaxDivisibleBy3SegmentsHelper(s, pos, current, count) >= 0
    decreases |s| - pos, |current| == 0
{
    if pos == |s| then
        if |current| == 0 then count else count
    else if |current| > 0 && IsDivisibleBy3(current) then
        var withSplit := MaxDivisibleBy3SegmentsHelper(s, pos, "", count + 1);
        var withoutSplit := MaxDivisibleBy3SegmentsHelper(s, pos + 1, current + [s[pos]], count);
        if withSplit > withoutSplit then withSplit else withoutSplit
    else
        MaxDivisibleBy3SegmentsHelper(s, pos + 1, current + [s[pos]], count)
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
    else (s[0] - '0') as int + SumOfDigits(s[1..])
}

function IntToString(n: int): string
    requires n >= 0
    ensures |IntToString(n)| > 0
    ensures forall i :: 0 <= i < |IntToString(n)| ==> '0' <= IntToString(n)[i] <= '9'
    ensures IntToString(n)[0] != '0' || |IntToString(n)| == 1
{
    if n == 0 then "0"
    else if n < 10 then [('0' as int + n) as char]
    else IntToString(n / 10) + [('0' as int + (n % 10)) as char]
}

method ComputeMaxDivisibleBy3Segments(s: string) returns (count: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures count == MaxDivisibleBy3Segments(s)
{
    count := 0;
    var pos := 0;
    var currentSum := 0;
    
    while pos < |s|
        invariant 0 <= pos <= |s|
        invariant count >= 0
        invariant currentSum >= 0
    {
        currentSum := currentSum + (s[pos] - '0') as int;
        pos := pos + 1;
        
        if currentSum % 3 == 0 {
            count := count + 1;
            currentSum := 0;
        }
    }
}

method ConvertIntToString(n: int) returns (s: string)
    requires n >= 0
    ensures s == IntToString(n)
    ensures |s| > 0
    ensures forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
{
    if n == 0 {
        s := "0";
    } else {
        s := "";
        var temp := n;
        while temp > 0
            invariant 0 <= temp <= n
        {
            var digit := temp % 10;
            s := [('0' as int + digit) as char] + s;
            temp := temp / 10;
        }
    }
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
    var count := ComputeMaxDivisibleBy3Segments(s);
    var countStr := ConvertIntToString(count);
    result := countStr + "\n";
}
// </vc-code>

