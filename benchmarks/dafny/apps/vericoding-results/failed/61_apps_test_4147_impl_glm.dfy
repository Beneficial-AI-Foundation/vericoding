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

// <vc-helpers>
function method split_lines(s: string): seq<string>
{
  if s == "" then []
  else if s[0] == '\n' then [""] + split_lines(s[1..])
  else
    var i := 0;
    while i < |s| && s[i] != '\n'
    {
      i := i + 1;
    }
    [s[..i]] + split_lines(s[i..])
}

function method parse_first_line_bamboo(line: string): (nat, nat, nat, nat)
  requires line != "" && line[|line|-1] == '\n'
{
  var tokens := split_by_space(line);
  assert |tokens| == 4;
  var N := string_to_nat(tokens[0]);
  var A := string_to_nat(tokens[1]);
  var B := string_to_nat(tokens[2]);
  var C := string_to_nat(tokens[3]);
  (N, A, B, C)
}

function method parse_bamboo_length(line: string): nat
  requires line != "" && line[|line|-1] == '\n'
{
  string_to_nat(line)
}

function method split_by_space(s: string): seq<string>
{
  if s == "" then []
  else if s[0] == ' ' then split_by_space(s[1..])
  else
    var i := 0;
    while i < |s| && s[i] != ' ' && s[i] != '\n'
    {
      i := i + 1;
    }
    [s[..i]] + split_by_space(s[i..])
}

function method string_to_nat(s: string): nat
{
  if s == "" then 0
  else
    var n := string_to_nat(s[1..]);
    if '0' <= s[0] <= '9' then
      n * 10 + (ord(s[0]) - ord('0')) as nat
    else
      n
}

function method nat_to_string(n: nat): string
{
  if n == 0 then "0"
  else 
    var s := "";
    var k := n;
    while k != 0
      invariant k <= n
    {
      s := (k % 10) as int + '0' + s;
      k := k / 10;
    }
    s
}

function method CompositionCostNonGhost(assignment: seq<nat>): nat
{
  var group_a_size := CountGroupMembersNonGhost(assignment, 1);
  var group_b_size := CountGroupMembersNonGhost(assignment, 2);
  var group_c_size := CountGroupMembersNonGhost(assignment, 3);
  (if group_a_size > 0 then (group_a_size - 1) * 10 else 0) +
  (if group_b_size > 0 then (group_b_size - 1) * 10 else 0) +
  (if group_c_size > 0 then (group_c_size - 1) * 10 else 0)
}

function method CountGroupMembersNonGhost(assignment: seq<nat>, group: nat): nat
{
  if |assignment| == 0 then 0
  else (if assignment[0] == group then 1 else 0) + CountGroupMembersNonGhost(assignment[1..], group)
}

function method CalculateGroupSumNonGhost(lengths: seq<nat>, assignment: seq<nat>, group: nat): nat
  requires |assignment| == |lengths|
{
  if |assignment| == 0 then 0
  else (if assignment[0] == group then lengths[0] else 0) + CalculateGroupSumNonGhost(lengths[1..], assignment[1..], group)
}

function method AdjustmentCostNonGhost(lengths: seq<nat>, assignment: seq<nat>, A: nat, B: nat, C: nat): nat
{
  var sum_a := CalculateGroupSumNonGhost(lengths, assignment, 1);
  var sum_b := CalculateGroupSumNonGhost(lengths, assignment, 2);
  var sum_c := CalculateGroupSumNonGhost(lengths, assignment, 3);
  AbsDiffNonGhost(sum_a, A) + AbsDiffNonGhost(sum_b, B) + AbsDiffNonGhost(sum_c, C)
}

function method AbsDiffNonGhost(a: nat, b: nat): nat
{
  if a >= b then a - b else b - a
}

function method CalculateAssignmentCostNonGhost(lengths: seq<nat>, assignment: seq<nat>, A: nat, B: nat, C: nat): nat
{
  CompositionCostNonGhost(assignment) + AdjustmentCostNonGhost(lengths, assignment, A, B, C)
}

function method GenerateAllAssignments(n: nat): seq<seq<nat>>
{
  if n == 0 then [[]]
  else
    var rec := GenerateAllAssignments(n-1);
    var result := [];
    foreach assignment in rec {
      result := result + [[1] + assignment, [2] + assignment, [3] + assignment];
    }
    result
}

predicate method HasAllThreeGroupsNonGhost(assignment: seq<nat>)
{
  (exists i :: 0 <= i < |assignment| && assignment[i] == 1) &&
  (exists i :: 0 <= i < |assignment| && assignment[i] == 2) &&
  (exists i :: 0 <= i < |assignment| && assignment[i] == 3)
}
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
  var input_with_newline := stdin_input + (if stdin_input[|stdin_input|-1] == '\n' then "" else "\n");
  var lines := split_lines(input_with_newline);
  var (N, A, B, C) := parse_first_line_bamboo(lines[0] + "\n");
  
  var lengths: seq<nat> := [];
  var i := 1;
  while i <= N
    invariant 1 <= i <= N+1
    invariant |lengths| == i-1
  {
    lengths := lengths + [parse_bamboo_length(lines[i] + "\n")];
    i := i + 1;
  }

  var all_assignments := GenerateAllAssignments(N);
  var min_cost: nat := 1000000;
  foreach assignment in all_assignments
  {
    if HasAllThreeGroupsNonGhost(assignment) {
      var cost := CalculateAssignmentCostNonGhost(lengths, assignment, A, B, C);
      if cost < min_cost {
        min_cost := cost;
      }
    }
  }

  return nat_to_string(min_cost) + "\n";
}
// </vc-code>

