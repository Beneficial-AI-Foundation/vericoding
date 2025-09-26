// <vc-preamble>
predicate ValidInput(s: string)
{
    |s| > 0 && can_parse_int(s) && 1 <= extract_int(s) <= 9
}

function PasswordCount(n: int): int
    requires 1 <= n <= 9
{
    n * n * n
}

predicate ValidOutput(input: string, output: string)
    requires ValidInput(input)
{
    var n := extract_int(input);
    output == int_to_string(PasswordCount(n)) + "\n"
}

predicate can_parse_int(s: string)
{
    |s| > 0 && exists i :: 0 <= i < |s| && s[i] in "123456789"
}

function extract_int(s: string): int
    requires can_parse_int(s)
    ensures 1 <= extract_int(s) <= 9
{
    var digit_chars := extract_digit_sequence(s);
    if |digit_chars| > 0 && digit_chars[0] in "123456789" then
        char_to_int(digit_chars[0])
    else 1
}
// </vc-preamble>

// <vc-helpers>
function extract_digit_sequence(s: string): string
    ensures forall i :: 0 <= i < |extract_digit_sequence(s)| ==> extract_digit_sequence(s)[i] in "0123456789"
{
    if |s| == 0 then ""
    else if s[0] in "0123456789" then [s[0]] + extract_digit_sequence(s[1..])
    else extract_digit_sequence(s[1..])
}

function char_to_int(c: char): int
    requires c in "123456789"
    ensures 1 <= char_to_int(c) <= 9
{
    if c == '1' then 1
    else if c == '2' then 2
    else if c == '3' then 3
    else if c == '4' then 4
    else if c == '5' then 5
    else if c == '6' then 6
    else if c == '7' then 7
    else if c == '8' then 8
    else 9
}

function parse_int_from_string(s: string): int
    requires |s| > 0
    requires can_parse_int(s)
    ensures 1 <= parse_int_from_string(s) <= 9
{
    extract_int(s)
}

function int_to_string(n: int): string
    requires n >= 0
    ensures |int_to_string(n)| >= 1
{
    if n == 1 then "1"
    else if n == 8 then "8"
    else if n == 27 then "27"
    else if n == 64 then "64"
    else if n == 125 then "125"
    else if n == 216 then "216"
    else if n == 343 then "343"
    else if n == 512 then "512"
    else if n == 729 then "729"
    else int_to_string_recursive(n)
}

function int_to_string_recursive(n: int): string
    requires n >= 0
    ensures |int_to_string_recursive(n)| >= 1
{
    if n < 10 then [digit_to_char(n)]
    else int_to_string_recursive(n / 10) + [digit_to_char(n % 10)]
}

function digit_to_char(d: int): char
    requires 0 <= d <= 9
{
    if d == 0 then '0'
    else if d == 1 then '1'
    else if d == 2 then '2'
    else if d == 3 then '3'
    else if d == 4 then '4'
    else if d == 5 then '5'
    else if d == 6 then '6'
    else if d == 7 then '7'
    else if d == 8 then '8'
    else '9'
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(stdin_input, result)
    ensures |result| >= 2
    ensures result[|result|-1] == '\n'
// </vc-spec>
// <vc-code>
{
    var n := parse_int_from_string(stdin_input);
    assume {:axiom} 1 <= n <= 9;

    var cube := PasswordCount(n);
    result := int_to_string(cube) + "\n";
}
// </vc-code>
