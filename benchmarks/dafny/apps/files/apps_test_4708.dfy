Calculate the total cost for N nights of accommodation with tiered pricing.
First K nights cost X yen each, remaining nights (if any) cost Y yen each.
Input: Four integers N, K, X, Y on separate lines.
Output: Single integer representing the total cost.

predicate ValidInput(input: string)
{
    var lines := SplitString(input, '\n');
    |lines| >= 4 &&
    IsValidInteger(lines[0]) &&
    IsValidInteger(lines[1]) &&
    IsValidInteger(lines[2]) &&
    IsValidInteger(lines[3]) &&
    var N := StringToInt(lines[0]);
    var K := StringToInt(lines[1]);
    var X := StringToInt(lines[2]);
    var Y := StringToInt(lines[3]);
    1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000
}

predicate ValidOutput(output: string, input: string)
{
    var lines := SplitString(input, '\n');
    if |lines| >= 4 && 
       IsValidInteger(lines[0]) &&
       IsValidInteger(lines[1]) &&
       IsValidInteger(lines[2]) &&
       IsValidInteger(lines[3]) then
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
        output == IntToString(expectedAns) + "\n"
    else
        output == ""
}

predicate IsValidInteger(s: string)
{
    |s| > 0 && (s[0] != '-' || |s| > 1) &&
    forall i :: 0 <= i < |s| ==> (i == 0 && s[i] == '-') || ('0' <= s[i] <= '9')
}

function SplitString(s: string, delimiter: char): seq<string>
{
    if |s| == 0 then
        []
    else
        SplitStringHelper(s, delimiter, 0, 0, [])
}

function SplitStringHelper(s: string, delimiter: char, start: int, current: int, acc: seq<string>): seq<string>
    requires 0 <= start <= |s|
    requires 0 <= current <= |s|
    requires start <= current
    decreases |s| - current
{
    if current >= |s| then
        if start < current then
            acc + [s[start..current]]
        else
            acc
    else if s[current] == delimiter then
        var part := s[start..current];
        SplitStringHelper(s, delimiter, current + 1, current + 1, acc + [part])
    else
        SplitStringHelper(s, delimiter, start, current + 1, acc)
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if s[0] == '-' then
        -StringToIntHelper(s[1..])
    else
        StringToIntHelper(s)
}

function StringToIntHelper(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then
        CharToDigit(s[0])
    else
        StringToIntHelper(s[..|s|-1]) * 10 + CharToDigit(s[|s|-1])
}

function CharToDigit(c: char): int
{
    if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

function IntToString(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelper(-n)
    else IntToStringHelper(n)
}

function IntToStringHelper(n: int): string
    requires n >= 0
{
    if n == 0 then ""
    else IntToStringHelper(n / 10) + [DigitToChar(n % 10)]
}

function DigitToChar(d: int): char
    requires 0 <= d <= 9
{
    ('0' as int + d) as char
}

method solve(input: string) returns (output: string)
    requires |input| > 0
    ensures ValidOutput(output, input)
    ensures ValidInput(input) ==> 
        var lines := SplitString(input, '\n');
        var N := StringToInt(lines[0]);
        var K := StringToInt(lines[1]);
        var X := StringToInt(lines[2]);
        var Y := StringToInt(lines[3]);
        1 <= N <= 10000 && 1 <= K <= 10000 && 1 <= Y < X <= 10000 ==>
        var expectedAns := if K < N then K * X + (N - K) * Y else N * X;
        output == IntToString(expectedAns) + "\n"
{
    var lines := SplitString(input, '\n');
    if |lines| < 4 {
        output := "";
        return;
    }

    if !IsValidInteger(lines[0]) || !IsValidInteger(lines[1]) || 
       !IsValidInteger(lines[2]) || !IsValidInteger(lines[3]) {
        output := "";
        return;
    }

    var N := StringToInt(lines[0]);
    var K := StringToInt(lines[1]);
    var X := StringToInt(lines[2]);
    var Y := StringToInt(lines[3]);

    var ans: int;
    if K < N {
        ans := K * X + (N - K) * Y;
    } else {
        ans := N * X;
    }

    output := IntToString(ans) + "\n";
}
