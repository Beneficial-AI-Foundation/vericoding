predicate ValidInput(s: string) 
{
    |s| == 7 && s[0] == 'A' && forall i :: 1 <= i < 7 ==> '0' <= s[i] <= '9'
}

function DigitSum(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    requires forall i :: start <= i < end ==> '0' <= s[i] <= '9'
    decreases end - start
{
    if start >= end then 0
    else (s[start] as int - '0' as int) + DigitSum(s, start + 1, end)
}

function ZeroCount(s: string, start: int, end: int): int
    requires 0 <= start <= end <= |s|
    decreases end - start
{
    if start >= end then 0
    else (if s[start] == '0' then 1 else 0) + ZeroCount(s, start + 1, end)
}

// <vc-helpers>
function method GetDigit(c: char): int
    requires '0' <= c <= '9'
    ensures 0 <= GetDigit(c) <= 9
{
    c as int - '0' as int
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: int)
    requires ValidInput(s)
    ensures result == DigitSum(s, 1, 7) + 9 * ZeroCount(s, 1, 7) + 1
// </vc-spec>
// <vc-code>
{
    var sum := 0;
    var zero_count := 0;
    for i := 1 to 6
        invariant 1 <= i <= 7
        invariant sum == DigitSum(s, 1, i)
        invariant zero_count == ZeroCount(s, 1, i)
    {
        sum := sum + GetDigit(s[i]);
        if s[i] == '0' {
            zero_count := zero_count + 1;
        }
    }
    result := sum + 9 * zero_count + 1;
}
// </vc-code>

