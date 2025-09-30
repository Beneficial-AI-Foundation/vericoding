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
function Digit(c: char): int
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

function CharToString(c: char): string
    requires '0' <= c <= '9'
{
    if c == '0' then "0"
    else if c == '1' then "1"
    else if c == '2' then "2"
    else if c == '3' then "3"
    else if c == '4' then "4"
    else if c == '5' then "5"
    else if c == '6' then "6"
    else if c == '7' then "7"
    else if c == '8' then "8"
    else "9"
}

function DigitToString(d: int): string
    requires 0 <= d <= 9
{
    if d == 0 then "0"
    else if d == 1 then "1"
    else if d == 2 then "2"
    else if d == 3 then "3"
    else if d == 4 then "4"
    else if d == 5 then "5"
    else if d == 6 then "6"
    else if d == 7 then "7"
    else if d == 8 then "8"
    else "9"
}

function SumMod3(s: string): int
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    ensures 0 <= SumMod3(s) < 3
    decreases |s|
{
    if |s| == 0 then 0 else (SumMod3(s[..|s|-1]) + Digit(s[|s|-1])) % 3
}

function MaxDivisibleBy3SegmentsHelper(s: string, pos: int, cur: string, cnt: int): int
    requires 0 <= pos <= |s|
    requires forall i :: 0 <= i < |s| ==> '0' <= s[i] <= '9'
    requires forall i :: 0 <= i < |cur| ==> '0' <= cur[i] <= '9'
    requires 0 <= cnt <= pos - |cur|
    ensures cnt <= MaxDivisibleBy3SegmentsHelper(s, pos, cur, cnt)
    ensures 0 <= MaxDivisibleBy3SegmentsHelper(s, pos, cur, cnt) <= |s|
    decreases |s| - pos
{
    if pos == |s| then
        if |cur| == 0 then cnt else if SumMod3(cur) == 0 then cnt + 1 else cnt
    else
        var ch := s[pos];
        if |cur| == 0 then
            if ch == '0' then MaxDivisibleBy3SegmentsHelper(s, pos+1, "", cnt+1)
            else MaxDivisibleBy3SegmentsHelper(s, pos+1, cur + CharToString(ch), cnt)
        else
            var newcur := cur + CharToString(ch);
            if SumMod3(newcur) == 0 then MaxDivisibleBy3SegmentsHelper(s, pos+1, "", cnt+1)
            else MaxDivisibleBy3SegmentsHelper(s, pos+1, newcur, cnt)
}

function IntToString(i: int): string
    requires i >= 0
    decreases i
{
    if i < 10 then DigitToString(i)
    else IntToString(i / 10) + DigitToString(i % 10)
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

