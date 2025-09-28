// <vc-preamble>
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
    0
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected parse error where `i < |s|` was on a new line. */
function parse_integer(s: string): nat
{
  var res := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant res == (if i == 0 then 0 else parse_integer_prefix(s, i))
  {
    res := res * 10 + (s[i] as int - '0' as int);
    i := i + 1;
  }
  return res;
}

function parse_integer_prefix(s: string, k: nat): nat
  requires 0 <= k <= |s|
  decreases k
{
  if k == 0 then 0 else parse_integer_prefix(s, k - 1) * 10 + (s[k - 1] as int - '0' as int)
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
/* code modified by LLM (iteration 5): No changes; previous fix for compilation error caused a regression. */
{
  var num_test_cases := get_test_count(stdin_input);
  var results: seq<string> := [];
  var i := 0;
  while i < num_test_cases
    invariant 0 <= i <= num_test_cases
    invariant |results| == i
  {
    var tc := get_test_case(stdin_input, i);
    var winning_moves := count_winning_first_moves(tc);
    results := results + [winning_moves as string];
    i := i + 1;
  }
  result := "";
  i := 0;
  while i < |results|
    invariant 0 <= i <= |results|
  {
    result := result + results[i] + "\n";
    i := i + 1;
  }
}
// </vc-code>
