Given an array of n integers, determine if it's possible to reorder the elements 
to make the double sum equal a target value m. The double sum is defined as
sum over i from 1 to n of (sum over j from i to n of a_j/j).
No elements may be added or removed from the array.

predicate valid_input_format(s: string)
{
    |s| >= 7 && 
    exists pos :: 0 < pos < |s| && s[pos] == '\n'
}

function get_test_count(stdin_input: string): int
    requires valid_input_format(stdin_input)
    ensures get_test_count(stdin_input) >= 1
{
    1
}

function get_array_sum(stdin_input: string, test_idx: int): int
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx < get_test_count(stdin_input)
{
    0
}

function get_target_m(stdin_input: string, test_idx: int): int
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx < get_test_count(stdin_input)
{
    0
}

function expected_output_for_input(stdin_input: string): string
    requires valid_input_format(stdin_input)
{
    compute_expected_output(stdin_input, 0, get_test_count(stdin_input))
}

predicate behavioral_correctness(stdin_input: string, result: string)
    requires valid_input_format(stdin_input)
{
    var T := get_test_count(stdin_input);
    count_responses(result) == T &&
    (forall i :: 0 <= i < T ==>
        var array_sum := get_array_sum(stdin_input, i);
        var target_m := get_target_m(stdin_input, i);
        var response := get_response_at_index(result, i);
        (array_sum == target_m <==> response == "YES\n") &&
        (array_sum != target_m <==> response == "NO\n"))
}

function compute_expected_output(stdin_input: string, current_test: int, total_tests: int): string
    requires valid_input_format(stdin_input)
    requires 0 <= current_test <= total_tests
    requires total_tests == get_test_count(stdin_input)
    decreases total_tests - current_test
{
    if current_test >= total_tests then ""
    else 
        var array_sum := get_array_sum(stdin_input, current_test);
        var target_m := get_target_m(stdin_input, current_test);
        var this_response := if array_sum == target_m then "YES\n" else "NO\n";
        this_response + compute_expected_output(stdin_input, current_test + 1, total_tests)
}

function get_response_at_index(result: string, idx: int): string
    requires idx >= 0
    ensures get_response_at_index(result, idx) in {"YES\n", "NO\n", ""}
{
    if idx == 0 then
        if |result| >= 4 && result[0..4] == "YES\n" then "YES\n"
        else if |result| >= 3 && result[0..3] == "NO\n" then "NO\n"
        else ""
    else if |result| >= 4 && result[0..4] == "YES\n" then get_response_at_index(result[4..], idx - 1)
    else if |result| >= 3 && result[0..3] == "NO\n" then get_response_at_index(result[3..], idx - 1)
    else if |result| >= 1 then get_response_at_index(result[1..], idx)
    else ""
}

function count_responses(s: string): int
    ensures count_responses(s) >= 0
{
    if |s| == 0 then 0
    else if |s| >= 4 && s[0..4] == "YES\n" then 1 + count_responses(s[4..])
    else if |s| >= 3 && s[0..3] == "NO\n" then 1 + count_responses(s[3..])
    else if |s| >= 1 then count_responses(s[1..])
    else 0
}

method solve(stdin_input: string) returns (result: string)
    requires valid_input_format(stdin_input)
    requires |stdin_input| > 0
    requires stdin_input != ""
    requires '\n' in stdin_input
    requires exists pos :: 0 <= pos < |stdin_input| && stdin_input[pos] == '\n'
    requires forall i :: 0 <= i < |stdin_input| ==> 
        stdin_input[i] in
{'0', '1', '2', '3', '4', '5', '6', '7', '8', '9', ' ', '\n', '-'}
