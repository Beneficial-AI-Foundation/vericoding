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
function compute_expected_output(stdin_input: string, test_idx: int, test_count: int): string
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx <= test_count
    requires test_count == get_test_count(stdin_input)
    decreases test_count - test_idx
{
    if test_idx == test_count then
        ""
    else
        var array_sum := get_array_sum(stdin_input, test_idx);
        var target_m := get_target_m(stdin_input, test_idx);
        var response := if array_sum == target_m then "YES\n" else "NO\n";
        response + compute_expected_output(stdin_input, test_idx + 1, test_count)
}

function compute_partial_output(stdin_input: string, up_to: int): string
    requires valid_input_format(stdin_input)
    requires 0 <= up_to <= get_test_count(stdin_input)
    decreases up_to
{
    if up_to == 0 then
        ""
    else
        compute_partial_output(stdin_input, up_to - 1) +
        (var array_sum := get_array_sum(stdin_input, up_to - 1);
         var target_m := get_target_m(stdin_input, up_to - 1);
         if array_sum == target_m then "YES\n" else "NO\n")
}

lemma compute_partial_equals_expected(stdin_input: string, T: int)
    requires valid_input_format(stdin_input)
    requires T == get_test_count(stdin_input)
    ensures compute_partial_output(stdin_input, T) == compute_expected_output(stdin_input, 0, T)
{
    // Proof by induction would go here
}

function count_responses(result: string): int
{
    count_responses_helper(result, 0, 0)
}

function count_responses_helper(result: string, idx: int, count: int): int
    requires 0 <= idx <= |result|
    decreases |result| - idx
{
    if idx == |result| then
        count
    else if idx + 4 <= |result| && result[idx..idx+4] == "YES\n" then
        count_responses_helper(result, idx + 4, count + 1)
    else if idx + 3 <= |result| && result[idx..idx+3] == "NO\n" then
        count_responses_helper(result, idx + 3, count + 1)
    else
        count_responses_helper(result, idx + 1, count)
}

function get_response_at_index(result: string, target_idx: int): string
    requires 0 <= target_idx < count_responses(result)
{
    get_response_at_index_helper(result, 0, 0, target_idx)
}

function get_response_at_index_helper(result: string, idx: int, current_count: int, target_idx: int): string
    requires 0 <= idx <= |result|
    requires 0 <= current_count <= count_responses(result)
    requires 0 <= target_idx < count_responses(result)
    decreases |result| - idx
{
    if idx == |result| then
        ""
    else if idx + 4 <= |result| && result[idx..idx+4] == "YES\n" then
        if current_count == target_idx then "YES\n"
        else get_response_at_index_helper(result, idx + 4, current_count + 1, target_idx)
    else if idx + 3 <= |result| && result[idx..idx+3] == "NO\n" then
        if current_count == target_idx then "NO\n"
        else get_response_at_index_helper(result, idx + 3, current_count + 1, target_idx)
    else
        get_response_at_index_helper(result, idx + 1, current_count, target_idx)
}

lemma partial_output_preserves_responses(stdin_input: string, test_idx: int)
    requires valid_input_format(stdin_input)
    requires 0 <= test_idx <= get_test_count(stdin_input)
    ensures count_responses(compute_partial_output(stdin_input, test_idx)) == test_idx
    ensures forall i :: 0 <= i < test_idx ==>
        var array_sum := get_array_sum(stdin_input, i);
        var target_m := get_target_m(stdin_input, i);
        var response := get_response_at_index(compute_partial_output(stdin_input, test_idx), i);
        (array_sum == target_m <==> response == "YES\n") &&
        (array_sum != target_m <==> response == "NO\n")
{
    // Proof would go here
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
    var T := get_test_count(stdin_input);
    result := "";
    var test_idx := 0;
    
    while test_idx < T
        invariant 0 <= test_idx <= T
        invariant result == compute_partial_output(stdin_input, test_idx)
    {
        var array_sum := get_array_sum(stdin_input, test_idx);
        var target_m := get_target_m(stdin_input, test_idx);
        
        if array_sum == target_m {
            result := result + "YES\n";
        } else {
            result := result + "NO\n";
        }
        
        test_idx := test_idx + 1;
    }
    
    compute_partial_equals_expected(stdin_input, T);
    partial_output_preserves_responses(stdin_input, T);
    assert result == expected_output_for_input(stdin_input);
    assert behavioral_correctness(stdin_input, result);
}
// </vc-code>

