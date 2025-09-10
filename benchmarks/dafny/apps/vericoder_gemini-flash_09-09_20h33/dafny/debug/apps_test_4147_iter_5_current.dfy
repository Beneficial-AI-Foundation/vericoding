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
ghost function CalculateGroupSum(input: string, assignment: seq<nat>, group: nat): nat
    requires ValidInput(input)
    requires ValidAssignment(input, assignment)
{
    var lines := split_lines(input);
    var (N, _, _, _) := parse_first_line_bamboo(lines[0]);
    var sum := 0;
    for i := 0 to N - 1
        invariant 0 <= i <= N
        invariant sum == sum_of_bamboo_lengths_in_group_prefix(input, assignment, group, i)
        invariant N == |assignment| // Add this invariant
    {
        if assignment[i] == group {
            sum := sum + parse_bamboo_length(lines[i+1]);
        }
    }
    return sum;
}

// Helper function to express the sum of bamboo lengths for a group up to an index `k`
ghost function sum_of_bamboo_lengths_in_group_prefix(input: string, assignment: seq<nat>, group: nat, k: nat): nat
    requires ValidInput(input)
    requires ValidAssignment(input, assignment)
    requires k <= |assignment|
    decreases k
{
    if k == 0 then 0
    else
        var prev_sum := sum_of_bamboo_lengths_in_group_prefix(input, assignment, group, k - 1);
        var lines := split_lines(input);
        if assignment[k-1] == group then
            prev_sum + parse_bamboo_length(lines[k])
        else
            prev_sum
}

// Removed the unused `MinGroupsRecursive` inductive predicate.

ghost function ValidAssignmentWithGroups(assignment: seq<nat>, N: nat): bool
{
    |assignment| == N &&
    (forall i :: 0 <= i < N ==> assignment[i] < 4) &&
    HasAllThreeGroups(assignment)
}

lemma {:induction N, i} FindMinCostPermutation(input: string, N: nat, A: nat, B: nat, C: nat, bamboos: seq<nat>): (assignment: seq<nat>, cost: nat)
    requires ValidInput(input)
    requires var lines := split_lines(input);
             var (N_parsed, A_parsed, B_parsed, C_parsed) := parse_first_line_bamboo(lines[0]);
             N == N_parsed && A == A_parsed && B == B_parsed && C == C_parsed &&
             bamboos == seq_from_function(N, i => parse_bamboo_length(lines[i+1]))
    ensures var (best_assignment, min_cost) := FindMinCostPermutation(input, N, A, B, C, bamboos);
            ValidAssignment(input, best_assignment) &&
            min_cost == CalculateAssignmentCost(input, best_assignment) &&
            (forall some_assignment :: ValidAssignment(input, some_assignment) ==>
                min_cost <= CalculateAssignmentCost(input, some_assignment))
    decreases N
{
    var min_cost := 4294967295; // Max possible nat value
    var best_assignment : seq<nat> := [];

    // For N >= 3, iterate all 3^N assignments.
    // 3^N assignments. Each cost calculation is O(N). Total O(N * 3^N).
    // For N <= 8, 3^8 = 6561, so 8 * 6561 = 52488 operations, which is feasible.
    var all_assignments := GenerateAllAssignments(N, 0, []);
    var current_min_cost_loop := 4294967295;
    var current_best_assignment_loop : seq<nat> := [];
    
    // Iteration over `all_assignments` needs to be done within a loop construct,
    // as Dafny's `forall var in collection` is for quantifiers, not iteration.
    // We can simulate it using a `for` loop over indices.
    for assign_idx := 0 to |all_assignments| - 1
        invariant 0 <= assign_idx <= |all_assignments|
        invariant (forall j :: 0 <= j < assign_idx && ValidAssignment(input, all_assignments[j]) ==> current_min_cost_loop <= CalculateAssignmentCost(input, all_assignments[j]))
        invariant current_min_cost_loop == (if assign_idx == 0 then 4294967295 else old(current_min_cost_loop) min (if ValidAssignment(input, all_assignments[assign_idx-1]) then CalculateAssignmentCost(input, all_assignments[assign_idx-1]) else 4294967295))
        invariant current_best_assignment_loop == (if assign_idx == 0 then [] else (if ValidAssignment(input, all_assignments[assign_idx-1]) && CalculateAssignmentCost(input, all_assignments[assign_idx-1]) < old(current_min_cost_loop) then all_assignments[assign_idx-1] else old(current_best_assignment_loop)))
    {
        var assign_candidate := all_assignments[assign_idx];
        if ValidAssignment(input, assign_candidate) {
            var current_cost := CalculateAssignmentCost(input, assign_candidate);
            if current_cost < current_min_cost_loop {
                current_min_cost_loop := current_cost;
                current_best_assignment_loop := assign_candidate;
            }
        }
    }
    return (current_best_assignment_loop, current_min_cost_loop);
}

ghost function GenerateAllAssignments(N: nat, k: nat, current_assignment: seq<nat>): seq<seq<nat>>
    requires k <= N
    requires |current_assignment| == k
    ensures forall s :: s in GenerateAllAssignments(N, k, current_assignment) ==> |s| == N
    decreases N - k
{
    if k == N then
        return [current_assignment];
    else
        var all_assignments: seq<seq<nat>> := [];
        for group := 1 to 3 {
             all_assignments := all_assignments + GenerateAllAssignments(N, k + 1, current_assignment + [group as nat]);
        }
        return all_assignments;
}

ghost function seq_from_function<T>(length: nat, f: nat ~> T): seq<T>
    requires forall i :: 0 <= i < length ==> f.requires(i)
    ensures |seq_from_function(length, f)| == length
{
    if length == 0 then []
    else seq_from_function(length - 1, f) + [f(length - 1)]
}

lemma lemma_string_to_int_non_negative(s: string)
    ensures string_to_int(s) >= 0
{}

lemma lemma_split_lines_valid(input: string)
    requires |input| > 0
    requires input[|input|-1] == '\n' || exists i :: 0 <= i < |input| && input[i] == '\n'
    ensures var lines := split_lines(input);
            forall i :: 0 <= i < |lines| ==> lines[i] != "" // Example property
{}

lemma lemma_parse_first_line_bamboo_properties(line: string)
    ensures var (N, A, B, C) := parse_first_line_bamboo(line); N >= 0 && A >= 0 && B >= 0 && C >= 0
{}

lemma lemma_parse_bamboo_length_properties(line: string)
    ensures parse_bamboo_length(line) >= 0
{}

lemma ValidInput_preserves_properties(input: string)
    requires ValidInput(input)
    ensures var lines := split_lines(input);
            var (N, A, B, C) := parse_first_line_bamboo(lines[0]);
            3 <= N <= 8 && 1 <= C < B < A <= 1000 && |lines| >= N + 1
            && (forall i :: 1 <= i <= N ==> parse_bamboo_length(lines[i]) >= 1)
{}

lemma ValidAssignment_group_properties(input: string, assignment: seq<nat>)
    requires ValidInput(input) && ValidAssignment(input, assignment)
    ensures var lines := split_lines(input);
            var (N, _, _, _) := parse_first_line_bamboo(lines[0]);
            |assignment| == N
            && (exists i :: 0 <= i < N && assignment[i] == 1)
            && (exists i :: 0 <= i < N && assignment[i] == 2)
            && (exists i :: 0 <= i < N && assignment[i] == 3)
{}
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
    var augmented_input := stdin_input + (if stdin_input[|stdin_input|-1] == '\n' then "" else "\n");
    lemma_split_lines_valid(augmented_input);
    var lines := split_lines(augmented_input);
    lemma_parse_first_line_bamboo_properties(lines[0]);
    var (N, A, B, C) := parse_first_line_bamboo(lines[0]);
    
    // We can pre-parse bamboo lengths once outside the main search loop.
    var bamboos: seq<nat>;
    if N > 0 { // To satisfy the requires clause of seq_from_function for f.requires(i) to be valid
        bamboos := seq_from_function(N, i => parse_bamboo_length(lines[i+1]));
    } else {
        bamboos := [];
    }

    var (best_assignment, min_cost) := FindMinCostPermutation(augmented_input, N, A, B, C, bamboos);
    
    lemma_string_to_int_non_negative(int_to_string(min_cost));
    result := int_to_string(min_cost) + "\n";
    return result;
}
// </vc-code>

