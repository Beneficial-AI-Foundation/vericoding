function int_to_string(i: int): string
    requires i >= 0
    ensures |int_to_string(i)| > 0
{
    "1"
}

function parse_int_from_string(s: string): int
    requires |s| > 0
    ensures parse_int_from_string(s) >= 1
{
    1
}

predicate ValidInput(stdin_input: string)
{
    |stdin_input| > 0
}

function sum_of_non_fizzbuzz_numbers(n: int): int
    requires n >= 0
    ensures sum_of_non_fizzbuzz_numbers(n) >= 0
    decreases n
{
    if n == 0 then 0
    else
        var num := n;
        if num % 3 > 0 && num % 5 > 0 then
            sum_of_non_fizzbuzz_numbers(n - 1) + num
        else
            sum_of_non_fizzbuzz_numbers(n - 1)
}

// <vc-helpers>
function power(base: int, exp: int): int
    requires exp >= 0
    decreases exp
{
    if exp == 0 then 1 else base * power(base, exp - 1)
}

function parse_int_correct(s: string): int
    requires |s| > 0
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires s[0] != '0' || |s| == 1
    decreases |s|
    ensures result >= 1
{
    if |s| == 1 then s[0] - '0'
    else ((s[0] - '0') * power(10, |s| - 1)) + parse_int_correct(s[1..])
}

function int_to_string_correct(i: int): string
    requires i >= 0
    decreases i
    ensures |result| > 0
{
    if i == 0 then "0"
    else int_to_string_correct(i / 10) + [(( ('0' as int) + (i % 10) ) as char)]
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| > 0
// </vc-spec>
// <vc-code>
function power(base: int, exp: int): int
    requires exp >= 0
    decreases exp
{
    if exp == 0 then 1 else base * power(base, exp - 1)
}

function parse_int_correct(s: string): int
    requires |s| > 0
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    requires s[0] != '0' || |s| == 1
    decreases |s|
    ensures result >= 1
{
    if |s| == 1 then s[0] - '0'
    else ((s[0] - '0') * power(10, |s| - 1)) + parse_int_correct(s[1..])
}

function int_to_string_correct(i: int): string
    requires i >= 0
    decreases i
    ensures |result| > 0
{
    if i == 0 then "0"
    else int_to_string_correct(i / 10) + [(( ('0' as int) + (i % 10) ) as char)]
}
// </vc-code>

