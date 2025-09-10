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
predicate is_winning_state(n: nat, x: nat, y: nat, z: nat, grundy: nat, memo: seq<nat>) {
    if n == 0 then grundy == 0 else
    grundy == (
        if n >= x then (set_to_seq({memo[n-x]})) else {} |
        if n >= y then (set_to_seq({memo[n-y]})) else {} |
        if n >= z then (set_to_seq({memo[n-z]})) else {}
    ).mex()
}

function compute_grundy_number(n: nat, x: nat, y: nat, z: nat, memo: seq<nat>): nat
    requires x >= 1 && y >= 1 && z >= 1
    requires forall i :: 0 <= i < n ==> is_winning_state(i, x, y, z, memo[i], memo)
    ensures is_winning_state(n, x, y, z, compute_grundy_number(n, x, y, z, memo), memo[0..n] + [compute_grundy_number(n, x, y, z, memo)])
{
    var moves: set<nat> := {};
    if n >= x then moves := moves + {memo[n-x]} else moves := moves;
    if n >= y then moves := moves + {memo[n-y]} else moves := moves;
    if n >= z then moves := moves + {memo[n-z]} else moves := moves;
    
    moves.mex()
}

function mex(s: seq<nat>): nat
    ensures forall i :: 0 <= i < mex(s) ==> i in s == false
    ensures mex(s) !in s
{
    var i: nat := 0;
    while i <= |s|
        invariant forall j :: 0 <= j < i ==> j in s == false
    {
        if i in s {
            i := i + 1;
        } else {
            return i;
        }
    }
    |s|
}

function method set_to_seq(s: set<nat>): seq<nat> {
    var result: seq<nat> := [];
    var i: nat := 0;
    while i <= set_max(s)
        invariant forall x :: x in s && x < i ==> x in result
        invariant |result| <= |s|
    {
        if i in s {
            result := result + [i];
        }
        i := i + 1;
    }
    result
}

function set_max(s: set<nat>): nat {
    if s == {} then 0
    else var max_val: nat :| max_val in s && forall x :: x in s ==> x <= max_val;
         max_val
}

function count_winning_moves_for_test_case(tc: TestCase): nat {
    var grundy: seq<nat> := [0];
    var i: nat := 1;
    
    while i <= tc.n
        invariant |grundy| == i
        invariant forall j :: 0 <= j < i ==> is_winning_state(j, tc.x, tc.y, tc.z, grundy[j], grundy)
    {
        grundy := grundy + [compute_grundy_number(i, tc.x, tc.y, tc.z, grundy)];
        i := i + 1;
    }
    
    var total_winning: nat := 0;
    var castle_grundy: nat := 0;
    var j: nat := 0;
    
    while j < tc.n
        invariant j <= tc.n
        invariant total_winning >= 0
    {
        castle_grundy := castle_grundy ^ grundy[tc.castles[j]];
        j := j + 1;
    }
    
    j := 0;
    while j < tc.n
        invariant j <= tc.n
        invariant total_winning >= 0
    {
        var new_grundy: nat := castle_grundy ^ grundy[tc.castles[j]];
        if new_grundy ^ grundy[abs(tc.castles[j] - tc.x)] == 0 then total_winning := total_winning + 1;
        if new_grundy ^ grundy[abs(tc.castles[j] - tc.y)] == 0 then total_winning := total_winning + 1;
        if new_grundy ^ grundy[abs(tc.castles[j] - tc.z)] == 0 then total_winning := total_winning + 1;
        j := j + 1;
    }
    
    total_winning
}

function abs(x: int): nat {
    if x < 0 then -x else x
}

function count_winning_first_moves(tc: TestCase): nat
    ensures count_winning_first_moves(tc) <= 3 * tc.n
{
    count_winning_moves_for_test_case(tc)
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
    var test_count := get_test_count(stdin_input);
    var result_lines: seq<string> := [];
    var i: nat := 0;
    
    while i < test_count
        invariant i <= test_count
        invariant |result_lines| == i
        invariant ValidOutput(stdin_input, "\n".join(result_lines) + (if |result_lines| > 0 then "\n" else ""))
    {
        var test_case := get_test_case(stdin_input, i);
        var winning_moves := count_winning_first_moves(test_case);
        result_lines := result_lines + [winning_moves.ToString()];
        i := i + 1;
    }
    
    result := "\n".join(result_lines) + "\n";
}
// </vc-code>

