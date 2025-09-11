// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0 && 
    var parts := ParseThreeIntsFunc(input);
    parts.1 > 0
}

function ParseThreeIntsFunc(s: string): (int, int, int)
    requires |s| > 0
{
    var nums := ParseNumbers(s, 0, [], 0, false);
    if |nums| >= 3 then (nums[0], if nums[1] > 0 then nums[1] else 1, nums[2])
    else (0, 1, 0)
}

function ParseNumbers(s: string, i: int, nums: seq<int>, current: int, inNumber: bool): seq<int>
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i >= |s| then
        if inNumber && |nums| < 3 then nums + [current] else nums
    else if |nums| >= 3 then
        nums
    else
        var c := s[i];
        if c >= '0' && c <= '9' then
            var digit := c as int - '0' as int;
            if !inNumber then
                ParseNumbers(s, i + 1, nums, digit, true)
            else
                ParseNumbers(s, i + 1, nums, current * 10 + digit, true)
        else if inNumber then
            ParseNumbers(s, i + 1, nums + [current], 0, false)
        else
            ParseNumbers(s, i + 1, nums, current, false)
}

function IntToStringFunc(n: int): string
{
    if n == 0 then "0"
    else if n < 0 then "-" + IntToStringHelperFunc(-n)
    else IntToStringHelperFunc(n)
}

function IntToStringHelperFunc(n: int): string
    requires n > 0
{
    if n < 10 then
        [('0' as int + n) as char]
    else
        IntToStringHelperFunc(n / 10) + [('0' as int + (n % 10)) as char]
}

function ComputeMaxValue(a: int, b: int, n: int): int
    requires b > 0
{
    var minVal := if b - 1 < n then b - 1 else n;
    (a * minVal) / b
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires |input| > 0
    requires ValidInput(input)
    ensures 
        var parts := ParseThreeIntsFunc(input);
        var a := parts.0;
        var b := parts.1;  
        var n := parts.2;
        b > 0 &&
        result == IntToStringFunc(ComputeMaxValue(a, b, n)) + "\n"
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
