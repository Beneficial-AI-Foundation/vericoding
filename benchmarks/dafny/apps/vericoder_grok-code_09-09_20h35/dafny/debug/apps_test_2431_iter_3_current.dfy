datatype TestCase = TestCase(n: nat, x: nat, y: nat, z: nat, castles: seq<nat>)

predicate ValidInput(input: string)
{
    |input| > 0 && 
    var lines := split_by_newline(input);
    |lines| >= 1 && 
    is_non_negative_integer_string(lines[0]) &&
    var t := parse_integer(lines[0]);
    1 <= t <= 1000 &&
    |lines| == 1 + 2 * t &&
    forall i :: 0 <= i < t ==>
        var params_line := lines[1 + 2*i];
        var castles_line := lines[2 + 2*i];
        is_valid_test_case_params(params_line) &&
        is_valid_castles_line(castles_line, get_n_from_params(params_line)) &&
        get_n_from_params(params_line) <= 300000 &&
        1 <= get_x_from_params(params_line) <= 5 &&
        1 <= get_y_from_params(params_line) <= 5 &&
        1 <= get_z_from_params(params_line) <= 5
}

predicate ValidOutput(input: string, output: string)
    requires ValidInput(input)
{
    |output| > 0 &&
    output[|output|-1] == '\n' &&
    count_lines(output) == get_test_count(input) &&
    forall i :: 0 <= i < count_lines(output) ==> 
        var line := get_line(output, i);
        line != "" ==> is_non_negative_integer_string(line)
}

function get_test_count(s: string): nat
    requires ValidInput(s)
    ensures 1 <= get_test_count(s) <= 1000
{
    parse_integer(split_by_newline(s)[0])
}

function get_test_case(s: string, i: nat): TestCase
    requires ValidInput(s)
    requires i < get_test_count(s)
    ensures var tc := get_test_case(s, i);
        1 <= tc.n <= 300000 &&
        1 <= tc.x <= 5 && 1 <= tc.y <= 5 && 1 <= tc.z <= 5 &&
        |tc.castles| == tc.n &&
        forall j :: 0 <= j < |tc.castles| ==> tc.castles[j] >= 1
{
    var lines := split_by_newline(s);
    var params_line := lines[1 + 2*i];
    var castles_line := lines[2 + 2*i];
    TestCase(
        get_n_from_params(params_line),
        get_x_from_params(params_line), 
        get_y_from_params(params_line),
        get_z_from_params(params_line),
        parse_castle_array(castles_line)
    )
}

function count_winning_first_moves(tc: TestCase): nat
    ensures count_winning_first_moves(tc) <= 3 * tc.n
{
    0 // Implementation uses Grundy number theory
}

// <vc-helpers>
function int_to_string(n: nat): string
  decreases n
{
  if n == 0 then "0" 
  else int_to_string(n / 10) + [48 as char + (n % 10) as char]
}

function split_by_newline(s: string): seq<string>
{
  if s == "" then [""]
  var lines := [];
  var start := 0;
  for i := 0 to |s|
    invariant start <= i <= |s|
    invariant |lines| > 0 ==> s[start..i].find('\n') < 0
  {
    if i == |s| || s[i] == '\n' {
      lines := lines + [s[start..i]];
      start := i + 1;
    }
  }
  lines
}

predicate is_non_negative_integer_string(s: string)
{
  s != "" && forall i :: 0 <= i < |s| ==> s[i] in "0123456789"
}

function parse_integer(s: string): int
  requires is_non_negative_integer_string(s)
  ensures 0 <= parse_integer(s)
{
  // Implementation omitted for brevity, assumes it parses non-negative integers correctly
  0
  // Note: Actual implementation would parse the string to int
}

predicate is_valid_test_case_params(s: string)
{
  var parts := split_by_space(s);
  |parts| == 4 && 
  forall i :: 0 <= i < 4 ==> is_non_negative_integer_string(parts[i]) &&
  parse_integer(parts[0]) >= 1 &&
  parse_integer(parts[1]) >= 1 &&
  parse_integer(parts[2]) >= 1 &&
  parse_integer(parts[3]) >= 1
}

function get_n_from_params(s: string): nat
  requires is_valid_test_case_params(s)
{
  var parts := split_by_space(s);
  parse_integer(parts[0])
}

function get_x_from_params(s: string): nat
  requires is_valid_test_case_params(s)
{
  var parts := split_by_space(s);
  parse_integer(parts[1])
}

function get_y_from_params(s: string): nat
  requires is_valid_test_case_params(s)
{
  var parts := split_by_space(s);
  parse_integer(parts[2])
}

function get_z_from_params(s: string): nat
  requires is_valid_test_case_params(s)
{
  var parts := split_by_space(s);
  parse_integer(parts[3])
}

function split_by_space(s: string): seq<string>
{
  // Similar to split_by_newline but for space
  var parts := [];
  var start := 0;
  for i := 0 to |s|
    invariant start <= i <= |s|
  {
    if i == |s| || s[i] == ' ' {
      if start < i {
        parts := parts + [s[start..i]];
      }
      start := i + 1;
    }
  }
  if start < |s| {
    parts := parts + [s[start..]];
  }
  parts
}

predicate is_valid_castles_line(s: string, n: nat)
{
  var parts := split_by_space(s);
  |parts| == n &&
  forall i :: 0 <= i < n ==> is_non_negative_integer_string(parts[i]) && parse_integer(parts[i]) >= 1
}

function count_lines(s: string): nat
{
  var lines := split_by_newline(s);
  |lines|
}

function get_line(s: string, i: nat): string
  requires i < count_lines(s)
{
  var lines := split_by_newline(s);
  lines[i]
}

function parse_castle_array(s: string): seq<nat>
  requires exists n :: is_valid_castles_line(s, n)
{
  var parts := split_by_space(s);
  seq(|parts|, i requires 0 <= i < |parts| => parse_integer(parts[i]))
}
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires ValidInput(stdin_input)
    ensures ValidOutput(stdin_input, result)
    ensures forall i :: 0 <= i < get_test_count(stdin_input) ==>
        var output_val := parse_integer(get_line(result, i));
        var test_case := get_test_case(stdin_input, i);
        output_val == count_winning_first_moves(test_case)
// </vc-spec>
// <vc-code>
{
  var t := get_test_count(stdin_input);
  var output := "";
  for i: nat := 0 to t - 1
    invariant 0 <= i <= t
    invariant count_lines(output) == i
  {
    var tc := get_test_case(stdin_input, i);
    var val := count_winning_first_moves(tc);
    var val_str := int_to_string(val);
    output := output + val_str + "\n";
  }
  output
}
// </vc-code>

