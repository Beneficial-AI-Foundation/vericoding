// <vc-preamble>
predicate CanPartitionIntoEqualSumSegments(input: string)
    requires |input| > 0
{
    var lines := SplitLines(input);
    if |lines| < 2 then false
    else
        var nStr := Trim(lines[0]);
        var digitsStr := Trim(lines[1]);
        var n := ParseInt(nStr);
        if n < 2 || n > 100 || |digitsStr| != n then false
        else
            var digits := ParseDigits(digitsStr);
            if |digits| != n then false
            else
                exists i {:trigger Sum(digits[..i + 1])} :: 0 <= i < n - 1 && 
                    var firstSum := Sum(digits[..i + 1]);
                    firstSum >= 0 &&
                    CanPartitionRemainder(digits, i + 1, firstSum)
}

predicate CanPartitionRemainder(digits: seq<int>, start: int, targetSum: int)
    requires 0 <= start <= |digits|
    requires targetSum >= 0
    decreases |digits| - start
{
    if start >= |digits| then true
    else
        exists segmentEnd :: start < segmentEnd <= |digits| && 
            Sum(digits[start..segmentEnd]) == targetSum &&
            CanPartitionRemainder(digits, segmentEnd, targetSum)
}

function Sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
}

function ParseInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else CharToDigit(s[0]) * Power10(|s| - 1) + ParseInt(s[1..])
}

function CharToDigit(c: char): int
    ensures CharToDigit(c) >= 0
{
    if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

function Power10(n: int): int
    requires n >= 0
{
    if n == 0 then 1 else 10 * Power10(n - 1)
}

function ParseDigits(s: string): seq<int>
    ensures forall j :: 0 <= j < |ParseDigits(s)| ==> ParseDigits(s)[j] >= 0
{
    if |s| == 0 then []
    else [CharToDigit(s[0])] + ParseDigits(s[1..])
}

function SplitLines(s: string): seq<string>
{
    SplitByChar(s, '\n')
}

function SplitByChar(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then [""]
    else if s[0] == delimiter then [""] + SplitByChar(s[1..], delimiter)
    else 
        var rest := SplitByChar(s[1..], delimiter);
        if |rest| == 0 then [s[..1]]
        else [s[..1] + rest[0]] + rest[1..]
}

function Trim(s: string): string
{
    TrimLeft(TrimRight(s))
}

function TrimLeft(s: string): string
{
    if |s| == 0 then s
    else if s[0] == ' ' || s[0] == '\t' || s[0] == '\n' || s[0] == '\r' then TrimLeft(s[1..])
    else s
}

function TrimRight(s: string): string
{
    if |s| == 0 then s
    else if s[|s| - 1] == ' ' || s[|s| - 1] == '\t' || s[|s| - 1] == '\n' || s[|s| - 1] == '\r' then TrimRight(s[..|s| - 1])
    else s
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires |s| > 0
    ensures result == "YES\n" || result == "NO\n"
    ensures result == "YES\n" <==> CanPartitionIntoEqualSumSegments(s)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
