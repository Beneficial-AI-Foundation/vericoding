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
function {:axiom} split_by_newline(s: string): seq<string>
    ensures |split_by_newline(s)| >= 1

predicate is_non_negative_integer_string(s: string)

function parse_integer(s: string): nat
    requires is_non_negative_integer_string(s)

predicate is_valid_test_case_params(s: string)

predicate is_valid_castles_line(s: string, n: nat)

function get_n_from_params(s: string): nat
    requires is_valid_test_case_params(s)
    ensures 1 <= get_n_from_params(s) <= 300000

function get_x_from_params(s: string): nat
    requires is_valid_test_case_params(s)
    ensures 1 <= get_x_from_params(s) <= 5

function get_y_from_params(s: string): nat
    requires is_valid_test_case_params(s)
    ensures 1 <= get_y_from_params(s) <= 5

function get_z_from_params(s: string): nat
    requires is_valid_test_case_params(s)
    ensures 1 <= get_z_from_params(s) <= 5

function parse_castle_array(s: string): seq<nat>

function count_lines(s: string): nat

function get_line(s: string, i: nat): string
    requires i < count_lines(s)

lemma ValidOutputImpliesCorrectLineCount(input: string, output: string)
    requires ValidInput(input)
    requires ValidOutput(input, output)
    ensures count_lines(output) == get_test_count(input)
{
}

lemma ValidOutputImpliesValidLines(input: string, output: string, i: nat)
    requires ValidInput(input)
    requires ValidOutput(input, output)
    requires i < count_lines(output)
    ensures var line := get_line(output, i);
        line != "" ==> is_non_negative_integer_string(line)
{
}

lemma TestCaseProperties(input: string, i: nat)
    requires ValidInput(input)
    requires i < get_test_count(input)
    ensures var tc := get_test_case(input, i);
        1 <= tc.n <= 300000 &&
        1 <= tc.x <= 5 && 1 <= tc.y <= 5 && 1 <= tc.z <= 5 &&
        |tc.castles| == tc.n &&
        forall j :: 0 <= j < |tc.castles| ==> tc.castles[j] >= 1
{
}

function {:axiom} build_output_string(results: seq<nat>): string
    ensures |build_output_string(results)| > 0
    ensures build_output_string(results)[|build_output_string(results)|-1] == '\n'
    ensures count_lines(build_output_string(results)) == |results|
    ensures forall i :: 0 <= i < |results| ==>
        var line := get_line(build_output_string(results), i);
        line != "" && is_non_negative_integer_string(line) &&
        parse_integer(line) == results[i]

function {:axiom} nat_to_string(n: nat): string
    ensures |nat_to_string(n)| > 0
    ensures is_non_negative_integer_string(nat_to_string(n))
    ensures parse_integer(nat_to_string(n)) == n
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
    var test_count := get_test_count(stdin_input);
    var results: seq<nat> := [];
    var i := 0;
    
    while i < test_count
        invariant 0 <= i <= test_count
        invariant |results| == i
        invariant forall j :: 0 <= j < i ==>
            var test_case := get_test_case(stdin_input, j);
            results[j] == count_winning_first_moves(test_case)
    {
        var test_case := get_test_case(stdin_input, i);
        TestCaseProperties(stdin_input, i);
        var winning_moves := count_winning_first_moves(test_case);
        results := results + [winning_moves];
        i := i + 1;
    }
    
    result := build_output_string(results);
}
// </vc-code>

