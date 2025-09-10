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
function count_responses(s: string): int
    ensures count_responses(s) >= 0
{
    if |s| == 0 then 0
    else (if s[0] == '\n' then 1 else 0) + count_responses(s[1..])
}

function get_response_at_index(s: string, idx: int): string
    requires 0 <= idx < count_responses(s)
{
    if idx == 0 then
        var first_newline := find_first_newline(s);
        s[..first_newline + 1]
    else
        get_response_at_index(s[find_first_newline(s) + 1..], idx - 1)
}

function find_first_newline(s: string): int
    requires '\n' in s
    ensures 0 <= find_first_newline(s) < |s|
    ensures s[find_first_newline(s)] == '\n'
    ensures forall i :: 0 <= i < find_first_newline(s) ==> s[i] != '\n'
{
    if s[0] == '\n' then 0
    else 1 + find_first_newline(s[1..])
}

function compute_expected_output(s: string, current_idx: int, total_tests: int): string
    requires valid_input_format(s)
    requires 0 <= current_idx <= total_tests
    ensures |compute_expected_output(s, current_idx, total_tests)| >= 0
{
    if current_idx >= total_tests then ""
    else 
        var array_sum := get_array_sum(s, current_idx);
        var target_m := get_target_m(s, current_idx);
        (if array_sum == target_m then "YES\n" else "NO\n")
        + compute_expected_output(s, current_idx + 1, total_tests)
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
    var pos := 0;
    var first_newline_idx := 0;
    while pos < |stdin_input| && stdin_input[pos] != '\n'
        invariant 0 <= pos <= |stdin_input|
        invariant forall i :: 0 <= i < pos ==> stdin_input[i] != '\n'
    {
        pos := pos + 1;
    }
    first_newline_idx := pos;
    
    var test_count_str := stdin_input[..first_newline_idx];
    var n := test_count_str as int;
    
    var result_str := "";
    var remainder := stdin_input[first_newline_idx + 1..];
    var test_idx := 0;
    
    while test_idx < n
        invariant test_idx >= 0
        invariant |result_str| >= 0
    {
        pos := 0;
        while pos < |remainder| && remainder[pos] != '\n'
            invariant 0 <= pos <= |remainder|
        {
            pos := pos + 1;
        }
        var line := remainder[..pos];
        
        var space_pos := 0;
        while space_pos < |line| && line[space_pos] != ' '
            invariant 0 <= space_pos <= |line|
        {
            space_pos := space_pos + 1;
        }
        var first_num_str := line[..space_pos];
        var second_num_str := line[space_pos + 1..];
        
        var first_num := first_num_str as int;
        var second_num := second_num_str as int;
        
        if first_num == second_num {
            result_str := result_str + "YES\n";
        } else {
            result_str := result_str + "NO\n";
        }
        
        remainder := remainder[pos + 1..];
        test_idx := test_idx + 1;
    }
    
    result := result_str;
}
// </vc-code>

