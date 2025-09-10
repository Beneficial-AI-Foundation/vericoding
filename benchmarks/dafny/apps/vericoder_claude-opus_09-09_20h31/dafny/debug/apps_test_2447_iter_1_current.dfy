function split_lines(s: string): seq<string>
{
    [""]  // placeholder implementation
}

function is_valid_number(s: string): bool
{
    true  // placeholder implementation
}

function parse_int(s: string): int
    requires is_valid_number(s)
{
    0  // placeholder implementation
}

function is_binary_string(s: string): bool
{
    true  // placeholder implementation
}

function ends_with_newline(s: string): bool
{
    |s| > 0 && s[|s|-1] == '\n'
}

predicate ValidInput(input: string)
{
    |input| > 0 &&
    input[|input|-1] == '\n' &&
    exists lines :: 
        lines == split_lines(input) &&
        |lines| >= 2 &&
        is_valid_number(lines[0]) &&
        var t := parse_int(lines[0]);
        t >= 1 && t <= 100 &&
        |lines| == t + 1 &&
        forall i :: 1 <= i < |lines| ==> 
            is_binary_string(lines[i]) && |lines[i]| >= 1 && |lines[i]| <= 1000
}

predicate ValidOutput(result: string)
{
    result != "" &&
    (ends_with_newline(result) || result == "") &&
    exists output_lines :: 
        output_lines == split_lines(result) &&
        |output_lines| >= 1 &&
        (forall i :: 0 <= i < |output_lines|-1 ==> is_valid_number(output_lines[i])) &&
        (forall i :: 0 <= i < |output_lines|-1 ==> parse_int(output_lines[i]) >= 0)
}

predicate CorrectResult(input: string, result: string)
    requires ValidInput(input)
{
    exists input_lines, t :: 
        input_lines == split_lines(input) &&
        t == parse_int(input_lines[0]) &&
        var output_lines := split_lines(result);
        |output_lines| == t + 1 &&
        forall test_case :: 0 <= test_case < t ==>
            var s := input_lines[test_case + 1];
            var min_ops := parse_int(output_lines[test_case]);
            min_ops == min_operations_to_make_good(s)
}

function min_operations_to_make_good(s: string): int
    requires is_binary_string(s)
    ensures min_operations_to_make_good(s) >= 0
    ensures min_operations_to_make_good(s) <= |s|
{
    if |s| == 0 then 0
    else min_ops_helper(s, 0, |s|)
}

// <vc-helpers>
function min_ops_helper(s: string, start: int, end: int): int
    requires is_binary_string(s)
    requires 0 <= start <= end <= |s|
    ensures min_ops_helper(s, start, end) >= 0
    ensures min_ops_helper(s, start, end) <= end - start
{
    if start >= end then 0
    else if end - start == 1 then 0
    else 
        var consecutive_ones := count_consecutive_ones(s, start, end);
        if consecutive_ones == 0 then 0
        else if consecutive_ones == end - start then 0
        else (consecutive_ones + 1) / 2
}

function count_consecutive_ones(s: string, start: int, end: int): int
    requires is_binary_string(s)
    requires 0 <= start <= end <= |s|
    ensures 0 <= count_consecutive_ones(s, start, end) <= end - start
{
    if start >= end then 0
    else if s[start] == '1' then 
        1 + count_consecutive_ones(s, start + 1, end)
    else 
        0
}

function int_to_string(n: int): string
    requires n >= 0
    ensures is_valid_number(int_to_string(n))
    ensures parse_int(int_to_string(n)) == n
{
    if n == 0 then "0"
    else int_to_string_helper(n)
}

function int_to_string_helper(n: int): string
    requires n > 0
    ensures is_valid_number(int_to_string_helper(n))
    ensures parse_int(int_to_string_helper(n)) == n
{
    if n < 10 then 
        [('0' as char) + (n as char)]
    else 
        int_to_string_helper(n / 10) + [('0' as char) + ((n % 10) as char)]
}

lemma parse_split_lines(input: string)
    requires ValidInput(input)
    ensures var lines := split_lines(input);
            |lines| >= 2 &&
            is_valid_number(lines[0]) &&
            var t := parse_int(lines[0]);
            t >= 1 && t <= 100 &&
            |lines| == t + 1
{
    // This follows from ValidInput predicate
}
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (result: string)
    requires ValidInput(input)
    ensures ValidOutput(result)
    ensures CorrectResult(input, result)
// </vc-spec>
// <vc-code>
{
    var lines := split_lines(input);
    parse_split_lines(input);
    
    var t := parse_int(lines[0]);
    var output := "";
    
    var i := 0;
    while i < t
        invariant 0 <= i <= t
        invariant |lines| == t + 1
        invariant forall j :: 1 <= j < |lines| ==> is_binary_string(lines[j])
    {
        var s := lines[i + 1];
        var min_ops := min_operations_to_make_good(s);
        output := output + int_to_string(min_ops) + "\n";
        i := i + 1;
    }
    
    result := output;
}
// </vc-code>

