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
function char_to_digit(c: char): nat
{
  (c as int) - ('0' as int)
}

function method_string_to_int(s: string): nat
{
  if s == "" then 0
  else method_string_to_int(s[..|s|-1]) * 10 + char_to_digit(s[|s|-1])
}

method SplitLines(s: string) returns (lines: seq<string>)
  ensures |lines| >= 1
  ensures forall i :: 0 <= i < |lines|-1 ==> lines[i] + "\n" in s
{
  lines := [];
  var start := 0;
  var end := 0;
  while end <= |s|
    invariant 0 <= start <= end <= |s|
    invariant forall i :: 0 <= i < |lines| ==> start > 0 || i == 0
    decreases |s| - end
  {
    if end < |s| && s[end] == '\n' {
      lines := lines + [s[start..end]];
      start := end + 1;
    }
    end := end + 1;
  }
  if start < |s| {
    lines := lines + [s[start..]];
  }
}

method SplitLine(line: string, sep: char) returns (parts: seq<string>)
{
  parts := [];
  var start := 0;
  var end := 0;
  while end <= |line|
    invariant 0 <= start <= end <= |line|
    decreases |line| - end
  {
    if end < |line| && line[end] == sep {
      parts := parts + [line[start..end]];
      start := end + 1;
    }
    end := end + 1;
  }
  if start < |line| {
    parts := parts + [line[start..]];
  }
}

method ParseFirst(line: string) returns (N: nat, A: nat, B: nat, C: nat)
{
  var parts := SplitLine(line, ' ');
  N := method_string_to_int(parts[0]);
  A := method_string_to_int(parts[1]);
  B := method_string_to_int(parts[2]);
  C := method_string_to_int(parts[3]);
}

function GroupSum(lengths: seq<nat>, assignment: seq<nat>, group: nat): nat
  requires |lengths| == |assignment|
{
  if |assignment| == 0 then 0
  else (if assignment[0] == group then lengths[0] else 0) + GroupSum(lengths[1..], assignment[1..], group)
}

function ComputeCost(lengths: seq<nat>, assignment: seq<nat>, A: nat, B: nat, C: nat): nat
  requires |lengths| == |assignment|
{
  var sum1 := GroupSum(lengths, assignment, 1);
  var sum2 := GroupSum(lengths, assignment, 2);
  var sum3 := GroupSum(lengths, assignment, 3);
  CompositionCost(assignment) + AbsDiff(sum1, A) + AbsDiff(sum2, B) + AbsDiff(sum3, C)
}

ghost predicate ValidAssignmentConcrete(lengths: seq<nat>, assignment: seq<nat>, A: nat, B: nat, C: nat)
  requires 3 <= |assignment| <= 8
{
  var lines := ["dummy"]; // Stub for ghost compatibility, not used in concrete logic
  |assignment| == |lengths| &&
  (forall i :: 0 <= i < |assignment| ==> 0 <= assignment[i] < 4) &&
  HasAllThreeGroups(assignment)
}

lemma ComputeCostMatches(lengths: seq<nat>, assignment: seq<nat>, A: nat, B: nat, C: nat)
  requires |lengths| == |assignment|
  requires ValidAssignmentConcrete(lengths, assignment, A, B, C)
  ensures ComposeConcreteCost(assignment) + AdjConcreteCost(lengths, assignment, A, B, C) == ComputeCost(lengths, assignment, A, B, C)
  decreases |assignment|
{}

// Helper for ComposeConcreteCost
function ComposeConcreteCost(assignment: seq<nat>): nat
{
  var group_a_size := CountGroupMembers(assignment, 1);
  var group_b_size := CountGroupMembers(assignment, 2);
  var group_c_size := CountGroupMembers(assignment, 3);
  (if group_a_size > 0 then (group_a_size - 1) * 10 else 0) +
  (if group_b_size > 0 then (group_b_size - 1) * 10 else 0) +
  (if group_c_size > 0 then (group_c_size - 1) * 10 else 0)
}

// Helper for AdjConcreteCost
function AdjConcreteCost(lengths: seq<nat>, assignment: seq<nat>, A: nat, B: nat, C: nat): nat
  requires |lengths| == |assignment|
{
  var sum_a := GroupSum(lengths, assignment, 1);
  var sum_b := GroupSum(lengths, assignment, 2);
  var sum_c := GroupSum(lengths, assignment, 3);
  AbsDiff(sum_a, A) + AbsDiff(sum_b, B) + AbsDiff(sum_c, C)
}

method FindMinCost(lengths: seq<nat>, A: nat, B: nat, C: nat, N: nat) returns (min_cost: nat)
  requires |lengths| == N
  requires 3 <= N <= 8
  ensures forall assignment: seq<nat> :: ValidAssignmentConcrete(lengths, assignment, A, B, C) ==> min_cost <= ComputeCost(lengths, assignment, A, B, C)
  ensures exists assignment: seq<nat> :: ValidAssignmentConcrete(lengths, assignment, A, B, C) && min_cost == ComputeCost(lengths, assignment, A, B, C)
{
  var total := 1;
  for _ := 0 to N-1 {
    total := total * 3;  // Use 3 groups (1,2,3) for valid assignments
  }
  var min_c := 0;  // Minimum possible cost to find
  var has_found := false;
  for assign_code := 0 to total - 1 {
    var assignment : seq<nat> := [];
    var temp := assign_code;
    var i := 0;
    while i < N {
      var g := temp % 3 + 1;  // Groups 1,2,3 only
      assignment := assignment + [g];
      temp := temp / 3;
      i := i + 1;
    }
    // All generated assignments have groups 1,2,3 since N>=3 and permuting, but check explicitly
    var has1 := false;
    var has2 := false;
    var has3 := false;
    for j := 0 to |assignment|-1 {
      if assignment[j] == 1 { has1 := true; }
      if assignment[j] == 2 { has2 := true; }
      if assignment[j] == 3 { has3 := true; }
    }
    if has1 && has2 && has3 {
      var cost := ComputeCost(lengths, assignment, A, B, C);
      ComputeCostMatches(lengths, assignment, A, B, C);  // Apply lemma to ensure match
      if !has_found || cost < min_c {
        min_c := cost;
        has_found := true;
      }
    }
  }
  min_cost := min_c;
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
  var input := stdin_input + (if stdin_input[|stdin_input|-1] == '\n' then "" else "\n");
  var lines := SplitLines(input);
  var first_line := lines[0];
  var (N, A, B, C) := ParseFirst(first_line);
  var lengths : seq<nat> := [];
  var i: nat := 1;
  while i <= N
    invariant 0 <= i <= N + 1
    invariant |lengths| == i - 1
  {
    var l := method_string_to_int(lines[i]);
    lengths := lengths + [l];
    i := i + 1;
  }
  var min_cost := FindMinCost(lengths, A, B, C, N);
  var result := int_to_string(min_cost) + "\n";
}
// </vc-code>

