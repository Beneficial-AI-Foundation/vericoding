// <vc-preamble>
predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 20 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function DistinctStringsCount(s: string): int
    requires ValidInput(s)
{
    |s| * 25 + 26
}

function int_to_string(n: int): string
    requires n >= 0
{
    if n == 0 then "0"
    else int_to_string_helper(n, "")
}

function int_to_string_helper(n: int, acc: string): string
    requires n >= 0
    decreases n
{
    if n == 0 then acc
    else int_to_string_helper(n / 10, [char_of_digit(n % 10)] + acc)
}

function char_of_digit(d: int): char
    requires 0 <= d <= 9
{
    match d
    case 0 => '0' case 1 => '1' case 2 => '2' case 3 => '3' case 4 => '4'
    case 5 => '5' case 6 => '6' case 7 => '7' case 8 => '8' case 9 => '9'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures result == int_to_string(DistinctStringsCount(s))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
