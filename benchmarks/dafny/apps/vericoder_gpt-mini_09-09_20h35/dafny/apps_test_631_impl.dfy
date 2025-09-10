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
  decreases |s|
{
  if |s| == 0 then 0
  else if |s| >= 4 && s[..4] == "YES\n" then 1 + count_responses(s[4..])
  else if |s| >= 3 && s[..3] == "NO\n" then 1 + count_responses(s[3..])
  else 0
}

function get_response_at_index(s: string, i: int): string
  requires 0 <= i < count_responses(s)
  decreases |s|
{
  if |s| >= 4 && s[..4] == "YES\n" then
    if i == 0 then "YES\n" else get_response_at_index(s[4..], i - 1)
  else if |s| >= 3 && s[..3] == "NO\n" then
    if i == 0 then "NO\n" else get_response_at_index(s[3..], i - 1)
  else ""  // unreachable under the precondition
}

function compute_expected_output(stdin_input: string, a: int, b: int): string
  requires valid_input_format(stdin_input)
  requires 0 <= a <= b
  requires b <= get_test_count(stdin_input)
  ensures count_responses(compute_expected_output(stdin_input, a, b)) == b - a
  decreases b - a
{
  if a >= b then ""
  else
    var resp := if get_array_sum(stdin_input, a) == get_target_m(stdin_input, a) then "YES\n" else "NO\n";
    resp + compute_expected_output(stdin_input, a + 1, b)
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
  result := compute_expected_output(stdin_input, 0, get_test_count(stdin_input));
  return;
}
// </vc-code>

