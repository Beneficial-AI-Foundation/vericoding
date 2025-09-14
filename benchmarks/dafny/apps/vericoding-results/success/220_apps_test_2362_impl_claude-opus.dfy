predicate valid_input_format(stdin_input: string)
{
  |stdin_input| > 0 && 
  has_valid_tree_structure(stdin_input) &&
  all_vertex_values_in_range(stdin_input) &&
  vertex_count_in_range(stdin_input)
}

predicate stdin_input_sum_equals_n(stdin_input: string)
  requires valid_input_format(stdin_input)
{
  sum_of_vertex_values(stdin_input) == get_vertex_count(stdin_input)
}

predicate has_common_prime_paths(stdin_input: string)
  requires valid_input_format(stdin_input)
{
  exists_path_with_common_prime_factor(stdin_input)
}

predicate no_common_prime_paths(stdin_input: string)
  requires valid_input_format(stdin_input)
{
  !has_common_prime_paths(stdin_input)
}

function max_common_prime_path_length(stdin_input: string): int
  requires valid_input_format(stdin_input)
  requires has_common_prime_paths(stdin_input)
  ensures max_common_prime_path_length(stdin_input) >= 1
{
  1
}

predicate has_valid_tree_structure(stdin_input: string)
{
  true
}

predicate all_vertex_values_in_range(stdin_input: string)
{
  true
}

predicate vertex_count_in_range(stdin_input: string)
{
  true
}

predicate exists_path_with_common_prime_factor(stdin_input: string)
  requires valid_input_format(stdin_input)
{
  true
}

function sum_of_vertex_values(stdin_input: string): int
  requires valid_input_format(stdin_input)
{
  0
}

function get_vertex_count(stdin_input: string): int
  requires valid_input_format(stdin_input)
  ensures get_vertex_count(stdin_input) >= 1
{
  1
}

function int_to_string(x: int): string
  requires x >= 0
  ensures |int_to_string(x)| > 0
{
  if x == 0 then "0"
  else if x < 10 then [char_of_digit(x)]
  else int_to_string(x / 10) + [char_of_digit(x % 10)]
}

function char_of_digit(d: int): char
  requires 0 <= d <= 9
{
  match d
    case 0 => '0' case 1 => '1' case 2 => '2' case 3 => '3' case 4 => '4'
    case 5 => '5' case 6 => '6' case 7 => '7' case 8 => '8' case 9 => '9'
}

// <vc-helpers>
// No additional helpers needed since the predicates and functions are already defined
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires valid_input_format(stdin_input)
  requires stdin_input[|stdin_input|-1] == '\n'
  ensures |result| > 0
  ensures result == "0" || (exists k: int :: k > 0 && result == int_to_string(k))
  ensures stdin_input_sum_equals_n(stdin_input) ==> result == "0"
  ensures !stdin_input_sum_equals_n(stdin_input) && no_common_prime_paths(stdin_input) ==> result == "0"
  ensures !stdin_input_sum_equals_n(stdin_input) && has_common_prime_paths(stdin_input) ==> 
    (exists k: int :: k >= 1 && result == int_to_string(k) && k == max_common_prime_path_length(stdin_input))
  ensures forall k: int :: k >= 0 && result == int_to_string(k) ==> k >= 0
  ensures result == "0" ==> (stdin_input_sum_equals_n(stdin_input) || no_common_prime_paths(stdin_input))
// </vc-spec>
// <vc-code>
{
  if stdin_input_sum_equals_n(stdin_input) {
    result := "0";
  } else if no_common_prime_paths(stdin_input) {
    result := "0";
  } else {
    // has_common_prime_paths(stdin_input) must be true here
    assert has_common_prime_paths(stdin_input);
    var max_length := max_common_prime_path_length(stdin_input);
    assert max_length >= 1;  // From the ensures clause of max_common_prime_path_length
    assert max_length > 0;   // Help the verifier see that >= 1 means > 0
    result := int_to_string(max_length);
    assert exists k: int :: k > 0 && result == int_to_string(k);  // Witness: k = max_length
  }
}
// </vc-code>

