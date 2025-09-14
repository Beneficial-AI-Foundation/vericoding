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

// <vc-helpers>
function compute_expected_output(stdin_input: string, start_idx: int, num_tests: int): string
    requires valid_input_format(stdin_input)
    requires 0 <= start_idx <= num_tests <= get_test_count(stdin_input)
    ensures compute_expected_output(stdin_input, start_idx, num_tests)[|compute_expected_output(stdin_input, start_idx, num_tests)|-1] == '\n'
    ensures forall i :: 0 <= i < num_tests - start_idx ==> get_response_at_index(compute_expected_output(stdin_input, start_idx, num_tests), i) in ["YES\n", "NO\n"]
{
    if start_idx == num_tests then
        ""
    else
        var array_sum := get_array_sum(stdin_input, start_idx);
        var target_m := get_target_m(stdin_input, start_idx);
        var response := if array_sum == target_m then "YES\n" else "NO\n";
        response + compute_expected_output(stdin_input, start_idx + 1, num_tests)
}

predicate is_newline(s: string, pos: int)
{
    0 <= pos < |s| && s[pos] == '\n'
}

function count_responses(result: string): int
    decreases |result|
{
    if |result| == 0 then 0
    else if result[0] == '\n' then count_responses(result[1:]) + 1
    else count_responses(result[1:])
}

function get_response_at_index(result: string, idx: int): string
    requires 0 <= idx < count_responses(result)
    requires count_responses(result) > 0
    decreases |result|
{
    if idx == 0 then take_until_newline(result)
    else get_response_at_index(drop_until_newline(result), idx-1)
}

function take_until_newline(s: string): string
    requires is_newline(s, pos) for some pos :: 0 <= pos <= |s|
    ensures is_newline(take_until_newline(s), |take_until_newline(s)| - 1)
    ensures forall k :: 0 <= k < |take_until_newline(s)| - 1 ==> !is_newline(take_until_newline(s), k)
    decreases |s|
{
    if |s| == 0 then ""
    else if s[0] == '\n' then "\n"
    else s[0] + take_until_newline(s[1..])
}

function drop_until_newline(s: string): string
    requires is_newline(s, pos) for some pos :: 0 <= pos <= |s|
    ensures |s| >= |drop_until_newline(s)|
    decreases |s|
{
    if |s| == 0 then ""
    else if s[0] == '\n' then s[1..]
    else drop_until_newline(s[1..])
}

function split_string_by_newline(s: string): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else 
        var line := take_until_newline(s);
        var rest := drop_until_newline(s);
        [line] + split_string_by_newline(rest)
}

function parse_string_to_int(s: string): int
    requires forall i :: 0 <= i < |s| ==> s[i] in '0'..'9'
    ensures parse_string_to_int(s) >= 0
    decreases |s|
{
    if |s| == 0 then 0
    else (if s[0] in '0'..'9' then (ord(s[0]) - ord('0')) * power(10, |s| - 1) else 0) + parse_string_to_int(s[1..])
}

function power(base: int, exp: int): int
    requires exp >= 0
    decreases exp
{
    if exp == 0 then 1 else base * power(base, exp - 1)
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires valid_input_format(stdin_input)
    requires |stdin_input| > 0
    requires stdin_input != ""
    requires '\n' in stdin_input
    requires exists pos :: 0 <= pos < |stdin_input| && stdin_input[pos] == '\n'
    requires forall i :: 0 <= i < |stdin_input| ==> 
        stdin_input[i] in
// </vc-spec>
// <vc-code>
{
    var lines := split_string_by_newline(stdin_input);
    var T := parse_string_to_int(lines[0]);
    var output := "";
    
    var test_idx := 0;
    while test_idx < T
        invariant 0 <= test_idx <= T
        invariant count_responses(output) == test_idx
        invariant forall i :: 0 <= i < test_idx ==>
            var sum_i := get_array_sum(stdin_input, i);
            var target_i := get_target_m(stdin_input, i);
            var resp_i := get_response_at_index(output, i);
            (sum_i == target_i <==> resp_i == "YES\n") &&
            (sum_i != target_i <==> resp_i == "NO\n")
    {
        var array_sum := get_array_sum(stdin_input, test_idx);
        var target_m := get_target_m(stdin_input, test_idx);
        
        if array_sum == target_m {
            output := output + "YES\n";
        } else {
            output := output + "NO\n";
        }
        
        test_idx := test_idx + 1;
    }
    
    result := output;
}
// </vc-code>

