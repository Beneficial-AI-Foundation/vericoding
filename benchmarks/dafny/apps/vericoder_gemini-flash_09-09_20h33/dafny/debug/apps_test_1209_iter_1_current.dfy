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
predicate {:opaque} well_formed_real_string(s: string) {
  s == "" || (s[0] == '-' && |s| > 1 && forall i :: 1 <= i < |s| && '0' <= s[i] <= '9') ||
  (s[0] >= '0' && s[0] <= '9' && forall i :: 1 <= i < |s| && '0' <= s[i] <= '9' )
}

lemma lemma_string_to_real_well_formed(s: string)
  requires well_formed_real_string(s)
  ensures s == "" || string_to_real(s) is real
{}

function string_to_int(s: string): (i: int)
  requires forall c :: c in s ==> '0' <= c <= '9' // Basic check, more robust needed for negative numbers

function method string_to_int_wrapper(s: string): int
  requires forall c :: c in s ==> '0' <= c <= '9'
  ensures string_to_int_wrapper(s) == string_to_int(s)
{
  var res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res == (if i == 0 then 0 else string_to_int(s[0..i]))
    decreases |s| - i
  {
    res := res * 10 + (s[i] - '0');
    i := i + 1;
  }
  return res;
}

function string_to_real(s: string): real
  requires forall c :: ('0' <= c <= '9' || c == '.' || c == '-')
{
  if s == "" then 0.0 else
  (
    var sign := 1.0;
    var start_index := 0;
    if s[0] == '-' then
      sign := -1.0;
      start_index := 1;
    else if s[0] == '+' then
      start_index := 1;

    var dot_index := -1;
    for k := start_index to |s|
      decreases |s| - k
    {
      if s[k] == '.' then
        dot_index := k;
        break;
    }

    var integer_part_str := "";
    var fractional_part_str := "";

    if dot_index == -1 then
      integer_part_str := s[start_index ..];
      fractional_part_str := "0";
    else
      integer_part_str := s[start_index .. dot_index];
      if dot_index + 1 < |s| then
        fractional_part_str := s[dot_index + 1 ..];
      else
        fractional_part_str := "0";

    var integer_part := if integer_part_str == "" then 0 else string_to_int_wrapper(integer_part_str);
    var fractional_part := if fractional_part_str == "" then 0 else string_to_int_wrapper(fractional_part_str);
    var fractional_scale := 1.0;
    for k := 0 to |fractional_part_str|
      decreases |fractional_part_str| - k
    {
      fractional_scale := fractional_scale * 10.0;
    }

    sign * (integer_part as real + (fractional_part as real / fractional_scale))
  )
}

function floor_of(r: real): int {
  if r >= 0.0 then r as int
  else if r as int == r then r as int
  else (r as int) - 1
}

function ceiling_of(r: real): int {
  if r >= 0.0 then if r as int == r then r as int else (r as int) + 1
  else r as int
}

function int_value_of(r: real): int
  requires is_integer(r)
{ r as int }

predicate is_integer(r: real) { r == r as int as real }

function count_lines(s: string): nat
  returns (count: nat)
  ensures count >= 0
{
  var c := 0;
  for i := 0 to |s|
    invariant 0 <= i <= |s|
    invariant c == count_char(s[0..i], '\n')
  {
    if i < |s| && s[i] == '\n' then
      c := c + 1;
    else if i == |s| && s[|s|-1] != '\n' then
      c := c + 1; // Count the last line even if it doesn't end with a newline
  }
  return c;
}

function count_char(s: string, c: char): nat
{
  var count := 0;
  for i := 0 to |s|-1
  {
    if s[i] == c then
      count := count + 1;
  }
  return count;
}

function get_n_from_input(input: string): nat
  requires contains_newline(input)
  requires first_line_is_valid_integer(input)
{
  var newline_idx := 0;
  while newline_idx < |input| && input[newline_idx] != '\n'
    invariant 0 <= newline_idx <= |input|
    decreases |input| - newline_idx
  {
    newline_idx := newline_idx + 1;
  }
  // The first line contains N
  var n_str := input[0 .. newline_idx];
  string_to_int_wrapper(n_str) as nat
}

function get_ith_line_start_and_end(s: string, i: nat): (start: nat, end: nat)
  requires 0 <= i < count_lines(s)
  ensures 0 <= start <= end <= |s|
{
  var current_line_start := 0;
  var current_line_idx := 0;
  var k := 0;
  while k < |s| && current_line_idx < i
    invariant 0 <= k <= |s|
    invariant 0 <= current_line_idx <= i
    decreases |s| - k
  {
    if s[k] == '\n' then
      current_line_start := k + 1;
      current_line_idx := current_line_idx + 1;
    k := k + 1;
  }

  var current_end := current_line_start;
  while current_end < |s| && s[current_end] != '\n'
    invariant current_line_start <= current_end <= |s|
    decreases |s| - current_end
  {
    current_end := current_end + 1;
  }
  return current_line_start, current_end;
}

function get_ith_line_content(s: string, i: nat): string
  requires 0 <= i < count_lines(s)
{
  var start, end := get_ith_line_start_and_end(s, i);
  s[start .. end]
}

function get_ith_real(input: string, i: nat): real
  requires 0 < i < count_lines(input) // For reals, typically 0th line is N
  requires remaining_lines_are_valid_reals(input)
{
  var line_content := get_ith_line_content(input, i);
  string_to_real(line_content)
}

function get_ith_integer(output: string, i: nat): int
  requires 0 <= i < count_lines(output)
  requires all_lines_are_integers(output)
{
  var line_content := get_ith_line_content(output, i);
  string_to_int_wrapper(line_content)
}

function sum_of_input_reals(input: string): real
  requires remaining_lines_are_valid_reals(input)
{
  var n := get_n_from_input(input);
  var sum := 0.0;
  for i := 0 to n
    invariant 0 <= i <= n
    invariant sum == (if i == 0 then 0.0 else sum_of_input_reals_upto(input, i-1))
  {
    sum := sum + get_ith_real(input, i + 1); // input lines are 1-indexed for reals
  }
  return sum;
}

function sum_of_input_reals_upto(input: string, k: nat): real
  requires 0 <= k < get_n_from_input(input)
  requires remaining_lines_are_valid_reals(input)
{
  if k == 0 then get_ith_real(input, 1)
  else sum_of_input_reals_upto(input, k-1) + get_ith_real(input, k+1)
}

function sum_of_output_integers(output: string): int
  requires all_lines_are_integers(output)
{
  var n := count_lines(output);
  var sum := 0;
  for i := 0 to n-1
    invariant 0 <= i <= n
    invariant sum == (if i == 0 then 0 else sum_of_output_integers_upto(output, i-1))
  {
    sum := sum + get_ith_integer(output, i);
  }
  return sum;
}

function sum_of_output_integers_upto(output: string, k: nat): int
  requires 0 <= k < count_lines(output)
  requires all_lines_are_integers(output)
{
  if k == 0 then get_ith_integer(output, 0)
  else sum_of_output_integers_upto(output, k-1) + get_ith_integer(output, k)
}
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
    var N := get_n_from_input(stdin_input);
    var X := new real[N];
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant forall k :: 0 <= k < i ==> X[k] == get_ith_real(stdin_input, k + 1)
    {
        X[i] := get_ith_real(stdin_input, i + 1);
        i := i + 1;
    }

    var Y := new int[N];
    var total_error := 0.0;
    i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant forall k :: 0 <= k < i ==> Y[k] == floor_of(X[k]) || Y[k] == ceiling_of(X[k])
        invariant total_error == sum_of_int_part_errors_upto(X, Y, i)
        invariant forall k :: 0 <= k < i ==> (is_integer(X[k]) ==> Y[k] == int_value_of(X[k]))
    {
        Y[i] := floor_of(X[i]);
        total_error := total_error + (X[i] - Y[i] as real);
        i := i + 1;
    }

    // Now distribute errors
    i := 0;
    while i < N && total_error > 0.0
        invariant 0 <= i <= N
        invariant total_error >= 0.0
        invariant forall k :: 0 <= k < i ==> Y[k] == floor_of(X[k]) || Y[k] == ceiling_of(X[k])
        invariant total_error == sum_of_int_part_errors_upto(X, Y, N) - sum_of_increments_upto(Y, X, i)
        invariant forall k :: 0 <= k < N && k < i ==> X[k] - Y[k] as real >= -0.0000001 // to avoid floating point issues
        invariant forall k :: 0 <= k < i ==> (is_integer(X[k]) ==> Y[k] == int_value_of(X[k]))
        decreases N - i
    {
        if X[i] - Y[i] as real > 0.0000001 && total_error > 0.0000001
            requires X[i] - Y[i] as real > 0.0000001
        {
            Y[i] := Y[i] + 1;
            total_error := total_error - 1.0;
        }
        i := i + 1;
    }
    
    // Construct the output string
    var sb := new System.Text.StringBuilder();
    i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant sb.Length >= 0
        invariant forall k :: 0 <= k < i ==> Y[k] == floor_of(X[k]) || Y[k] == ceiling_of(X[k])
        invariant forall k :: 0 <= k < i ==> (is_integer(X[k]) ==> Y[k] == int_value_of(X[k]))
    {
        sb.Append(Y[i].ToString());
        sb.Append('\n');
        i := i + 1;
    }

    output := sb.ToString();
    return output;
}

function sum_of_int_part_errors_upto(X: array<real>, Y: array<int>, idx: nat): real
  requires X.Length == Y.Length
  requires idx <= X.Length
{
  var sum := 0.0;
  for k := 0 to idx
    invariant 0 <= k <= idx
    invariant sum == (if k == 0 then 0.0 else sum_of_int_part_errors_upto_loop(X, Y, k-1))
  {
    sum := sum + (X[k] - Y[k] as real);
  }
  return sum;
}

function sum_of_int_part_errors_upto_loop(X: array<real>, Y: array<int>, k: nat): real
  requires X.Length == Y.Length
  requires k < X.Length
{
  if k == 0 then (X[0] - Y[0] as real)
  else sum_of_int_part_errors_upto_loop(X, Y, k-1) + (X[k] - Y[k] as real)
}

function sum_of_increments_upto(Y: array<int>, X: array<real>, idx: nat): real
  requires X.Length == Y.Length
  requires idx <= X.Length
{
  var sum := 0.0;
  for k := 0 to idx
    invariant 0 <= k <= idx
    invariant sum == (if k == 0 then 0.0 else sum_of_increments_upto_loop(Y, X, k-1))
  {
    if X[k] - floor_of(X[k]) as real > 0.0000001 then
        sum := sum + 1.0;
  }
  return sum;
}

function sum_of_increments_upto_loop(Y: array<int>, X: array<real>, k: nat): real
  requires X.Length == Y.Length
  requires k < X.Length
{
  if k == 0 then (if X[0] - floor_of(X[0]) as real > 0.0000001 then 1.0 else 0.0)
  else sum_of_increments_upto_loop(Y, X, k-1) + (if X[k] - floor_of(X[k]) as real > 0.0000001 then 1.0 else 0.0)
}
// </vc-code>

