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
function NaturalParseInt(s: string): (i: int)
    requires |s| > 0
    requires forall k :: 0 <= k < |s| ==> '0' <= s[k] <= '9'
    ensures i >= 0
{
    if |s| == 1 then
        (s[0] - '0')
    else
        (NaturalParseInt(s[..|s|-1]) * 10) + (s[|s|-1] - '0')
}

function power(base: int, exp: int): int
    requires exp >= 0
    ensures power(base, exp) >= 0
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}


function int_to_string_positive(i: int): string
    requires i > 0
    ensures |int_to_string_positive(i)| > 0
    ensures forall k :: 0 <= k < |int_to_string_positive(i)| ==> '0' <= int_to_string_positive(i)[k] <= '9'
    decreases i
{
    if i == 0 then
        "0"
    else if i < 10 then
        var c := '0' + i;
        c as string
    else
        var lastDigit := i % 10;
        var remaining := i / 10;
        int_to_string_positive(remaining) + (('0' + lastDigit) as string)
}

function {:id "int_to_string_wrapper"} int_to_string_wrapper(i: int): string
    requires i >= 0
    ensures |int_to_string_wrapper(i)| > 0
    ensures (i == 0) ==> (int_to_string_wrapper(i) == "0")
{
    if i == 0 then
        "0"
    else
        int_to_string_positive(i)
}

lemma lemma_int_to_string_positive_length(i: int)
    requires i > 0
    ensures var s := int_to_string_positive(i);
            var len := |s|;
            len > 0
    ensures (i >= 0) ==> (i < 10) ==> (|int_to_string_positive(i)| == 1)
    ensures (i >= 10) ==> (|int_to_string_positive(i)| == |int_to_string_positive(i / 10)| + 1)
{
    if i < 10 && i > 0 {
        assert |int_to_string_positive(i)| == 1; // Base case for length
    } else if i >= 10 {
        lemma_int_to_string_positive_length(i / 10);
        assert |int_to_string_positive(i)| == |int_to_string_positive(i / 10)| + 1; // Recursive step
    }
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures |result| > 0
// </vc-spec>
// <vc-code>
{
    // Validate and parse the input from stdin_input
    var n := NaturalParseInt(stdin_input);

    // Calculate sum of non-FizzBuzz numbers using the provided function
    var sum := sum_of_non_fizzbuzz_numbers(n);

    // Convert the sum to a string
    result := int_to_string_wrapper(sum);
}
// </vc-code>

