// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed parsing error by explicitly adding `else` clause at the `if s == "YES\n" || s == "NO\n" then count := 1` line. */
function count_responses(s: string): int
    ensures count_responses(s) >= 0
{
    var count := 0;
    if "YES\n" in s || "NO\n" in s then {
        if s == "YES\n" || s == "NO\n" then count := 1
        else if s matches "YES\n" + _ || s matches "NO\n" + _ then
        {
            var newline_pos := 0;
            while newline_pos < |s|
                invariant 0 <= newline_pos <= |s|
            {
                var next_newline := s.IndexOf('\n', newline_pos);
                if next_newline == -1 then
                    break;
                count := count + 1;
                newline_pos := next_newline + 1;
            }
        } else {
             // case where neither "YES\n" nor "NO\n" is explicitly found at the beginning, but somewhere in the string
        }
    } else {
        // s does not contain "YES\n" or "NO\n"
    }
    return count;
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
/* code modified by LLM (iteration 5): Fixed the loop invariant for prev_nl_count and removed the incorrect invariant for the string content of result. */
{
    var T := get_test_count(stdin_input);
    var i := 0;
    result := "";

    while i < T
        invariant 0 <= i <= T
        invariant forall k :: 0 <= k < i ==> (
                      var array_sum_k := get_array_sum(stdin_input, k);
                      var target_m_k := get_target_m(stdin_input, k);
                      var response_k := if array_sum_k == target_m_k then "YES\n" else "NO\n";
                      var current_response_start_idx := 0;
                      var j := 0;
                      while j < k
                          invariant 0 <= j <= k
                          decreases k - j
                      {
                          var prev_array_sum_j := get_array_sum(stdin_input, j);
                          var prev_target_m_j := get_target_m(stdin_input, j);
                          var prev_response_j_len := if prev_array_sum_j == prev_target_m_j then 4 else 3;
                          current_response_start_idx := current_response_start_idx + prev_response_j_len;
                          j := j + 1;
                      }
                      current_response_start_idx + |response_k| <= |result| &&
                      result[current_response_start_idx .. current_response_start_idx + |response_k|] == response_k
                  )
    {
        var array_sum := get_array_sum(stdin_input, i);
        var target_m := get_target_m(stdin_input, i);

        if array_sum == target_m {
            result := result + "YES\n";
        } else {
            result := result + "NO\n";
        }
        i := i + 1;
    }
}
// </vc-code>
