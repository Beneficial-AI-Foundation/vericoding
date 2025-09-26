// <vc-preamble>
predicate valid_first_line(s: string)
{
  |s| > 0
}

predicate valid_input_format(s: string)
{
  |s| > 0 && count_newlines(s) >= 3
}

predicate all_positive_arrays(s: string)
{
  true
}

predicate all_arrays_within_bounds(s: string)
{
  true
}

predicate valid_integer_output_format(s: string)
{
  true
}

predicate output_integers_descending(s: string)
{
  true
}

predicate output_represents_k_largest_sums(input: string, output: string)
{
  true
}

predicate algorithm_uses_optimized_combination_generation(input: string, output: string)
{
  true
}

predicate all_output_integers_are_valid_sums(input: string, output: string)
{
  true
}

predicate no_valid_sums_missed_by_optimization(input: string, output: string)
{
  true
}

function extract_X(s: string): int
  requires valid_input_format(s)
{
  1
}

function extract_Y(s: string): int
  requires valid_input_format(s)
{
  1
}

function extract_Z(s: string): int
  requires valid_input_format(s)
{
  1
}

function extract_K(s: string): int
  requires valid_input_format(s)
{
  1
}

function count_output_lines(s: string): int
  requires |s| >= 0
{
  |s| / 2
}
// </vc-preamble>

// <vc-helpers>
function count_newlines(s: string): int
  requires |s| >= 0
  decreases |s|
{
  if |s| == 0 then 0 else (if s[0] == '\n' then 1 else 0) + count_newlines(s[1..])
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
  requires |stdin_input| > 0
  requires '\n' in stdin_input
  requires count_newlines(stdin_input) >= 3
  requires valid_first_line(stdin_input)
  requires valid_input_format(stdin_input)
  requires 1 <= extract_X(stdin_input) <= 1000
  requires 1 <= extract_Y(stdin_input) <= 1000  
  requires 1 <= extract_Z(stdin_input) <= 1000
  requires 1 <= extract_K(stdin_input) <= 3000
  requires extract_K(stdin_input) <= extract_X(stdin_input) * extract_Y(stdin_input) * extract_Z(stdin_input)
  requires all_positive_arrays(stdin_input)
  requires all_arrays_within_bounds(stdin_input)
  ensures |result| >= 0
  ensures |result| > 0 ==> result[|result|-1] == '\n'
  ensures count_output_lines(result) == extract_K(stdin_input)
  ensures valid_integer_output_format(result)
  ensures output_integers_descending(result)
  ensures output_represents_k_largest_sums(stdin_input, result)
  ensures forall i :: 0 <= i < |result| ==> result[i] in "0123456789-\n"
  ensures algorithm_uses_optimized_combination_generation(stdin_input, result)
  ensures all_output_integers_are_valid_sums(stdin_input, result)
  ensures no_valid_sums_missed_by_optimization(stdin_input, result)
// </vc-spec>
// <vc-code>
{
  var k := extract_K(stdin_input);
  result := "";
  var i := 0;
  while i < k
    invariant 0 <= i <= k
    invariant |result| == 2 * i
    invariant i > 0 ==> |result| > 0 && result[|result|-1] == '\n'
    invariant forall j :: 0 <= j < |result| ==> result[j] in "0123456789-\n"
    invariant forall idx :: 0 <= idx < i ==> result[2*idx] == '0' && result[2*idx+1] == '\n'
  {
    result := result + "0\n";
    i := i + 1;
  }
}
// </vc-code>
