// <vc-preamble>

predicate ValidInput(n: int) {
    n >= 0
}

function sum_of_numbers_in_string(s: string): int
{
    var numbers := extract_numbers_from_string(s);
    sum_sequence(numbers)
}

function extract_numbers_from_string(s: string): seq<int>
{
    extract_numbers_helper(s, 0, 0, false, [])
}

function sum_sequence(numbers: seq<int>): int
{
    if |numbers| == 0 then 0
    else numbers[0] + sum_sequence(numbers[1..])
}
function extract_numbers_helper(s: string, i: int, current_number: int, in_number: bool, numbers: seq<int>): seq<int>
    decreases |s| - i
    requires 0 <= i <= |s|
    requires current_number >= 0
{
    if i == |s| then
        if in_number then numbers + [current_number] else numbers
    else
        var c := s[i];
        if '0' <= c <= '9' then
            var digit := c as int - '0' as int;
            extract_numbers_helper(s, i + 1, current_number * 10 + digit, true, numbers)
        else
            if in_number then
                extract_numbers_helper(s, i + 1, 0, false, numbers + [current_number])
            else
                extract_numbers_helper(s, i + 1, 0, false, numbers)
}

method extract_numbers_from_string_imperative(s: string) returns (numbers: seq<int>)
    ensures numbers == extract_numbers_from_string(s)
{
    numbers := [];
    var current_number := 0;
    var in_number := false;
    var i := 0;

    while i < |s|
        invariant 0 <= i <= |s|
        invariant current_number >= 0
        invariant !in_number ==> current_number == 0
        invariant extract_numbers_helper(s, i, current_number, in_number, numbers) == extract_numbers_from_string(s)
    {
        var c := s[i];
        if '0' <= c <= '9' {
            var digit := c as int - '0' as int;
            current_number := current_number * 10 + digit;
            in_number := true;
        } else {
            if in_number {
                numbers := numbers + [current_number];
                current_number := 0;
                in_number := false;
            }
        }
        i := i + 1;
    }

    if in_number {
        numbers := numbers + [current_number];
    }

    assert numbers == extract_numbers_from_string(s);
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method fruit_distribution(s: string, n: int) returns (mangoes: int)
    requires ValidInput(n)
    ensures mangoes == n - sum_of_numbers_in_string(s)
    ensures mangoes >= 0 <==> n >= sum_of_numbers_in_string(s)
// </vc-spec>
// <vc-code>
{
    var sum := sum_of_numbers_in_string(s);
    mangoes := n - sum;
}
// </vc-code>
