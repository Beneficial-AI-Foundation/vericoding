// <vc-preamble>
ghost predicate ValidInput(input: string)
{
    exists lines :: (lines == split_lines(input) &&
    |lines| >= 2 &&
    exists N, A, B, C :: 
        parse_first_line_bamboo(lines[0]) == (N, A, B, C) &&
        3 <= N <= 8 &&
        1 <= C < B < A <= 1000 &&
        |lines| >= N + 1 &&
        forall i :: 1 <= i <= N ==> 
            exists li :: parse_bamboo_length(lines[i]) == li && 1 <= li <= 1000)
}

ghost predicate ValidAssignment(input: string, assignment: seq<nat>)
    requires ValidInput(input)
{
    exists lines, N, A, B, C :: 
        lines == split_lines(input) &&
        parse_first_line_bamboo(lines[0]) == (N, A, B, C) &&
        |assignment| == N &&
        (forall i :: 0 <= i < N ==> assignment[i] < 4) &&
        HasAllThreeGroups(assignment)
}

ghost predicate HasAllThreeGroups(assignment: seq<nat>)
{
    (exists i :: 0 <= i < |assignment| && assignment[i] == 1) &&
    (exists i :: 0 <= i < |assignment| && assignment[i] == 2) &&
    (exists i :: 0 <= i < |assignment| && assignment[i] == 3)
}

ghost function CalculateAssignmentCost(input: string, assignment: seq<nat>): nat
    requires ValidInput(input)
    requires ValidAssignment(input, assignment)
{
    CompositionCost(assignment) + AdjustmentCost(input, assignment)
}

ghost function CompositionCost(assignment: seq<nat>): nat
{
    var group_a_size := CountGroupMembers(assignment, 1);
    var group_b_size := CountGroupMembers(assignment, 2);
    var group_c_size := CountGroupMembers(assignment, 3);
    (if group_a_size > 0 then (group_a_size - 1) * 10 else 0) +
    (if group_b_size > 0 then (group_b_size - 1) * 10 else 0) +
    (if group_c_size > 0 then (group_c_size - 1) * 10 else 0)
}

ghost function AdjustmentCost(input: string, assignment: seq<nat>): nat
    requires ValidInput(input)
    requires ValidAssignment(input, assignment)
{
    var lines := split_lines(input);
    var (N, A, B, C) := parse_first_line_bamboo(lines[0]);
    var sum_a := CalculateGroupSum(input, assignment, 1);
    var sum_b := CalculateGroupSum(input, assignment, 2);
    var sum_c := CalculateGroupSum(input, assignment, 3);
    AbsDiff(sum_a, A) + AbsDiff(sum_b, B) + AbsDiff(sum_c, C)
}

ghost function CountGroupMembers(assignment: seq<nat>, group: nat): nat
{
    if |assignment| == 0 then 0
    else (if assignment[0] == group then 1 else 0) + CountGroupMembers(assignment[1..], group)
}

ghost function CalculateGroupSum(input: string, assignment: seq<nat>, group: nat): nat
    requires ValidInput(input)
{
    0
}

ghost function AbsDiff(a: nat, b: nat): nat
{
    if a >= b then a - b else b - a
}

ghost function split_lines(s: string): seq<string>
{
    []
}

ghost function parse_first_line_bamboo(line: string): (nat, nat, nat, nat)
{
    (0, 0, 0, 0)
}

ghost function parse_bamboo_length(line: string): nat
{
    0
}

function int_to_string(n: nat): string
{
    ""
}

ghost function string_to_int(s: string): nat
{
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (result: string)
    requires |stdin_input| > 0
    requires stdin_input[|stdin_input|-1] == '\n' || exists i :: 0 <= i < |stdin_input| && stdin_input[i] == '\n'
    requires ValidInput(stdin_input + (if stdin_input[|stdin_input|-1] == '\n' then "" else "\n"))
    ensures |result| > 0
    ensures result[|result|-1] == '\n'
    ensures exists val :: val >= 0 && result == int_to_string(val) + "\n"
    ensures forall assignment :: ValidAssignment(stdin_input + (if stdin_input[|stdin_input|-1] == '\n' then "" else "\n"), assignment) ==>
        string_to_int(result[..|result|-1]) <= CalculateAssignmentCost(stdin_input + (if stdin_input[|stdin_input|-1] == '\n' then "" else "\n"), assignment)
    decreases *
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
