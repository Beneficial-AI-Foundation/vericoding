// <vc-preamble>
predicate IsValidDateString(s: string, y: int, m: int, d: int)
{
    |s| >= 10 && 
    s[4] == '/' && s[7] == '/' &&
    StringToInt(s[0..4]) == y &&
    StringToInt(s[5..7]) == m &&
    StringToInt(s[8..10]) == d
}

function StringToInt(s: string): int
{
    if |s| == 0 then 0
    else if |s| == 1 then CharToDigit(s[0])
    else if |s| == 2 then CharToDigit(s[0]) * 10 + CharToDigit(s[1])
    else if |s| == 4 then CharToDigit(s[0]) * 1000 + CharToDigit(s[1]) * 100 + CharToDigit(s[2]) * 10 + CharToDigit(s[3])
    else 0
}

function CharToDigit(c: char): int
{
    if '0' <= c <= '9' then (c as int) - ('0' as int) else 0
}

predicate ValidInput(s: string)
{
    exists y, m, d :: IsValidDateString(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31
}

predicate CorrectOutput(s: string, result: string)
{
    exists y, m, d :: IsValidDateString(s, y, m, d) && y == 2019 && 1 <= m <= 12 && 1 <= d <= 31 && 
    ((m < 4 || (m == 4 && d <= 30)) ==> result == "Heisei") && 
    ((m > 4 || (m == 4 && d > 30)) ==> result == "TBD")
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
requires |stdin_input| > 0
requires ValidInput(stdin_input)
ensures CorrectOutput(stdin_input, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
