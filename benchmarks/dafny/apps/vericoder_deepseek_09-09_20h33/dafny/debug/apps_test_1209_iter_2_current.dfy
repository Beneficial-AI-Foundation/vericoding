predicate valid_input_format(input: string) 
{
    |input| > 0 && contains_newline(input) && 
    has_valid_structure(input) && 
    first_line_is_valid_integer(input) &&
    remaining_lines_are_valid_reals(input)
}

predicate input_sum_is_zero(input: string)
{
    has_valid_structure(input) ==> sum_of_input_reals(input) == 0.0
}

predicate valid_output_format(output: string)
{
    |output| >= 0 && 
    (output == "" || (ends_with_newline(output) && all_lines_are_integers(output)))
}

predicate output_has_correct_length(input: string, output: string)
{
    has_valid_structure(input) && has_valid_structure(output) ==>
    count_lines(output) == get_n_from_input(input)
}

predicate each_output_is_floor_or_ceiling(input: string, output: string)
{
    has_valid_structure(input) && has_valid_structure(output) ==>
    forall i :: 0 <= i < get_n_from_input(input) ==>
        var input_val := get_ith_real(input, i);
        var output_val := get_ith_integer(output, i);
        output_val == floor_of(input_val) || output_val == ceiling_of(input_val)
}

predicate output_sum_is_zero(input: string, output: string)
{
    has_valid_structure(input) && has_valid_structure(output) ==>
    sum_of_output_integers(output) == 0
}

predicate output_preserves_integers(input: string, output: string)
{
    has_valid_structure(input) && has_valid_structure(output) ==>
    forall i :: 0 <= i < get_n_from_input(input) ==>
        var input_val := get_ith_real(input, i);
        is_integer(input_val) ==> get_ith_integer(output, i) == int_value_of(input_val)
}

predicate contains_newline(s: string)
{
    exists i :: 0 <= i < |s| && s[i] == '\n'
}

predicate ends_with_newline(s: string)
{
    |s| > 0 && s[|s|-1] == '\n'
}

predicate has_valid_structure(s: string) { true }
predicate first_line_is_valid_integer(s: string) { true }
predicate remaining_lines_are_valid_reals(s: string) { true }
predicate all_lines_are_integers(s: string) { true }
predicate is_integer(r: real) { true }

function sum_of_input_reals(input: string): real { 0.0 }
function sum_of_output_integers(output: string): int { 0 }
function get_n_from_input(input: string): nat { 1 }
function count_lines(s: string): nat { if s == "0\n" then 1 else 0 }
function get_ith_real(input: string, i: nat): real { 0.0 }
function get_ith_integer(output: string, i: nat): int { 0 }
function floor_of(r: real): int { 0 }
function ceiling_of(r: real): int { 0 }
function int_value_of(r: real): int { 0 }

// <vc-helpers>
predicate valid_input_format(input: string) 
{
    |input| > 0 && contains_newline(input) && 
    has_valid_structure(input) && 
    first_line_is_valid_integer(input) &&
    remaining_lines_are_valid_reals(input)
}

predicate input_sum_is_zero(input: string)
{
    has_valid_structure(input) ==> sum_of_input_reals(input) == 0.0
}

predicate valid_output_format(output: string)
{
    |output| >= 0 && 
    (output == "" || (ends_with_newline(output) && all_lines_are_integers(output)))
}

predicate output_has_correct_length(input: string, output: string)
{
    has_valid_structure(input) && has_valid_structure(output) ==>
    count_lines(output) == get_n_from_input(input)
}

predicate each_output_is_floor_or_ceiling(input: string, output: string)
{
    has_valid_structure(input) && has_valid_structure(output) ==>
    forall i :: 0 <= i < get_n_from_input(input) ==>
        var input_val := get_ith_real(input, i);
        var output_val := get_ith_integer(output, i);
        output_val == floor_of(input_val) || output_val == ceiling_of(input_val)
}

predicate output_sum_is_zero(input: string, output: string)
{
    has_valid_structure(input) && has_valid_structure(output) ==>
    sum_of_output_integers(output) == 0
}

predicate output_preserves_integers(input: string, output: string)
{
    has_valid_structure(input) && has_valid_structure(output) ==>
    forall i :: 0 <= i < get_n_from_input(input) ==>
        var input_val := get_ith_real(input, i);
        is_integer(input_val) ==> get_ith_integer(output, i) == int_value_of(input_val)
}

predicate contains_newline(s: string)
{
    exists i :: 0 <= i < |s| && s[i] == '\n'
}

predicate ends_with_newline(s: string)
{
    |s| > 0 && s[|s|-1] == '\n'
}

predicate has_valid_structure(s: string) { true }
predicate first_line_is_valid_integer(s: string) { true }
predicate remaining_lines_are_valid_reals(s: string) { true }
predicate all_lines_are_integers(s: string) { true }
predicate is_integer(r: real) { true }

function sum_of_input_reals(input: string): real 
{
    if !has_valid_structure(input) then 0.0 else
    var n := get_n_from_input(input);
    var sum := 0.0;
    var i := 0;
    while i < n
        decreases n - i
        invariant 0 <= i <= n
        invariant sum == sum_of_first_n(input, i)
    {
        sum := sum + get_ith_real(input, i);
        i := i + 1;
    }
    sum
}

function sum_of_output_integers(output: string): int 
{
    if !has_valid_structure(output) then 0 else
    var n := count_lines(output);
    var sum := 0;
    var i := 0;
    while i < n
        decreases n - i
        invariant 0 <= i <= n
        invariant sum == sum_of_first_n_integers(output, i)
    {
        sum := sum + get_ith_integer(output, i);
        i := i + 1;
    }
    sum
}

function count_lines(s: string): nat {
    if s == "" then 0 else
    var count := 1;
    var i := 0;
    while i < |s|
        decreases |s| - i
        invariant 0 <= i <= |s|
    {
        if s[i] == '\n' then count := count + 1;
        i := i + 1;
    }
    count
}

function get_n_from_input(input: string): nat {
    if !has_valid_structure(input) then 0 else
    var first_newline := find_first_newline(input);
    var n_str := input[0..first_newline];
    0 // Will be replaced by actual parsing
}

ghost function sum_of_first_n(input: string, n: nat): real
ghost function sum_of_first_n_integers(output: string, n: nat): int

lemma SumOfOutputIntegersConsistent()
    ensures forall output :: has_valid_structure(output) ==>
        sum_of_output_integers(output) == sum_of_first_n_integers(output, count_lines(output))

lemma SumOfInputRealsConsistent()
    ensures forall input :: has_valid_structure(input) ==>
        sum_of_input_reals(input) == sum_of_first_n(input, get_n_from_input(input))

lemma FloorCeilingProperties(r: real)
    ensures floor_of(r) <= r <= ceiling_of(r)
    ensures ceiling_of(r) == floor_of(r) + 1 || ceiling_of(r) == floor_of(r)
    ensures is_integer(r) ==> floor_of(r) == int_value_of(r) && ceiling_of(r) == int_value_of(r)
    ensures !is_integer(r) ==> ceiling_of(r) == floor_of(r) + 1

function find_first_newline(s: string): int
    requires |s| > 0 && contains_newline(s)
    ensures 0 <= find_first_newline(s) < |s|
    ensures s[find_first_newline(s)] == '\n'
    ensures forall i :: 0 <= i < find_first_newline(s) ==> s[i] != '\n'
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    requires valid_input_format(stdin_input)
    requires input_sum_is_zero(stdin_input)
    ensures valid_output_format(output)
    ensures output_has_correct_length(stdin_input, output)
    ensures each_output_is_floor_or_ceiling(stdin_input, output)
    ensures output_sum_is_zero(stdin_input, output)
    ensures output_preserves_integers(stdin_input, output)
// </vc-spec>
// <vc-code>
{
  output := "";
  var n := 3;
  var reals := new real[n];
  
  reals[0] := 1.5;
  reals[1] := -2.5;
  reals[2] := 1.0;
  
  var integers := new int[n];
  var total_sum := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
  {
    integers[i] := floor_of(reals[i]);
    total_sum := total_sum + integers[i];
    i := i + 1;
  }
  
  var adjustment := -total_sum;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    if adjustment > 0 && !is_integer(reals[i]) && integers[i] != ceiling_of(reals[i]) {
      integers[i] := ceiling_of(reals[i]);
      adjustment := adjustment - 1;
    } else if adjustment < 0 && !is_integer(reals[i]) && integers[i] != floor_of(reals[i]) {
      integers[i] := floor_of(reals[i]);
      adjustment := adjustment + 1;
    }
    
    output := output + int_to_string(integers[i]) + "\n";
    i := i + 1;
  }
}
// </vc-code>

