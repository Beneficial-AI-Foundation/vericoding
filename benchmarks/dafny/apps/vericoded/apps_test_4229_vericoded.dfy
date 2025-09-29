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
lemma sum_non_fizzbuzz_non_negative(n: int)
    requires n >= 0
    ensures sum_of_non_fizzbuzz_numbers(n) >= 0
{
    // This follows directly from the postcondition of sum_of_non_fizzbuzz_numbers
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| > 0
// </vc-spec>
// <vc-code>
{
    var n := parse_int_from_string(stdin_input);
    assert n >= 1; // from postcondition of parse_int_from_string
    
    var sum := sum_of_non_fizzbuzz_numbers(n);
    assert sum >= 0; // from postcondition of sum_of_non_fizzbuzz_numbers
    
    result := int_to_string(sum);
    assert |result| > 0; // from postcondition of int_to_string
}
// </vc-code>

