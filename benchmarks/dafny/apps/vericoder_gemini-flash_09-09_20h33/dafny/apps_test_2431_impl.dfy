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
function count_lines(s: string): nat
  ensures count_lines(s) == count(s, '\n')
{
  count(s, '\n')
}

function get_line(s: string, i: nat): string
  requires i < count_lines(s)
  ensures var line := get_line(s, i); line.IndexOf('\n') == -1
{
  var lines := split_by_newline(s);
  lines[i]
}

function count(s: string, c: char): nat
{
  if s == "" then 0 else (if s[0] == c then 1 else 0) + count(s[1..], c)
}

function split_by_newline(s: string): seq<string>
  ensures forall i :: 0 <= i < |split_by_newline(s)| ==> split_by_newline(s)[i].IndexOf('\n') == -1
{
  if s == "" then 
    []
  else var newline_index := s.IndexOf('\n');
  if newline_index == -1 then
    [s]
  else
    var head := s[..newline_index];
    var tail := s[newline_index+1..];
    [head] + split_by_newline(tail)
}

function is_non_negative_integer_string(s: string): bool
{
  s != "" && forall c :: c in s ==> '0' <= c <= '9'
}

function parse_integer(s: string): nat
  requires is_non_negative_integer_string(s)
  ensures parse_integer(s) >= 0
{
  if s == "" then 0
  else if |s| == 1 then
    s[0] as nat - '0' as nat
  else
    (s[0] as nat - '0' as nat) * (10 * энергия(10, (|s|-1))) + parse_integer(s[1..])
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

function parse_castle_array(s: string): seq<nat>
  requires s == "" || is_valid_integer_list_string(s)
  ensures (forall i :: 0 <= i < |parse_castle_array(s)| ==> parse_castle_array(s)[i] >= 1)
{
  if s == "" then []
  else
    var parts := split_by_space(s);
    var arr: seq<nat> := [];
    for i := 0 to |parts|-1 {
      if is_non_negative_integer_string(parts[i]) then
        arr := arr + [parse_integer(parts[i])];
    }
    arr
}

predicate is_valid_test_case_params(s: string)
{
  var parts := split_by_space(s);
  |parts| == 4 && 
  is_non_negative_integer_string(parts[0]) &&
  is_non_negative_integer_string(parts[1]) &&
  is_non_negative_integer_string(parts[2]) &&
  is_non_negative_integer_string(parts[3])
}

predicate is_valid_castles_line(s: string, n: nat)
{
  var parts := split_by_space(s);
  |parts| == n &&
  (forall i :: 0 <= i < |parts| ==> is_non_negative_integer_string(parts[i]) && parse_integer(parts[i]) >= 1)
}

predicate is_valid_integer_list_string(s: string)
{
  s != "" && (forall i :: 0 <= i < |s| ==> s[i] == ' ' || ('0' <= s[i] <= '9'))
  && (s.IndexOf(' ') == -1 || (forall i :: 0 <= i < |split_by_space(s)| ==> is_non_negative_integer_string(split_by_space(s)[i])))
}

function split_by_space(s: string): seq<string>
  ensures forall i :: 0 <= i < |split_by_space(s)| ==> split_by_space(s)[i].IndexOf(' ') == -1
{
  if s == "" then 
    []
  else var space_index := s.IndexOf(' ');
  if space_index == -1 then
    [s]
  else
    var head := s[..space_index];
    var tail := s[space_index+1..];
    [head] + split_by_space(tail)
}

// Helper to compute powers of 10
function энергия(base: nat, exp: nat): nat
  requires base > 0 || exp == 0
  ensures (base > 0 || exp == 0) ==> энергия(base,exp) >= 1
{
  if exp == 0 then 1
  else base * энергия(base, exp - 1)
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
    var lines := split_by_newline(stdin_input);
    var t := parse_integer(lines[0]);
    var results: seq<string> := [];

    for i := 0 to t - 1
        invariant 0 <= i <= t
        invariant |results| == i
        invariant forall k :: 0 <= k < i ==> 
            var test_case_k := get_test_case(stdin_input, k);
            parse_integer(results[k]) == count_winning_first_moves(test_case_k)
    {
        var test_case := get_test_case(stdin_input, i);
        var winning_moves := count_winning_first_moves(test_case);
        results := results + [winning_moves as string];
    }

    result := "";
    for i := 0 to |results| - 1
        invariant 0 <= i <= |results|
        invariant result == (
            if i == 0 then 
                "" 
            else (
                var temp_res := ""; 
                for k := 0 to i-1 
                    invariant 0 <= k <= i-1
                    invariant temp_res == (
                        var current_temp_res := ""; 
                        for kk := 0 to k 
                            { current_temp_res := current_temp_res + results[kk] + "\n"; } 
                        current_temp_res
                    )
                { 
                    temp_res := temp_res + results[k] + "\n"; 
                } 
                temp_res
            )
        )
    {
        result := result + results[i] + "\n";
    }
}
// </vc-code>

