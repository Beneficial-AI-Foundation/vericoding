predicate valid_input_format(stdin_input: string)
{
    var lines := split_lines_func(stdin_input);
    |lines| >= 2 &&
    var first_line := split_spaces_func(lines[0]);
    var second_line := split_spaces_func(lines[1]);
    |first_line| == 2 &&
    is_valid_integer(first_line[0]) &&
    is_valid_integer(first_line[1]) &&
    var N := string_to_int_func(first_line[0]);
    var A := string_to_int_func(first_line[1]);
    1 <= N <= 50 &&
    1 <= A <= 50 &&
    |second_line| == N &&
    (forall j | 0 <= j < |second_line| :: 
        is_valid_integer(second_line[j]) &&
        1 <= string_to_int_func(second_line[j]) <= 50)
}

predicate is_valid_output(output: string)
{
    |output| > 1 && 
    output[|output|-1] == '\n' &&
    var result_str := output[..|output|-1];
    is_valid_integer(result_str) &&
    string_to_int_func(result_str) >= 0
}

predicate output_represents_correct_count(stdin_input: string, output: string)
    requires valid_input_format(stdin_input)
    requires is_valid_output(output)
{
    var lines := split_lines_func(stdin_input);
    var first_line := split_spaces_func(lines[0]);
    var second_line := split_spaces_func(lines[1]);
    var N := string_to_int_func(first_line[0]);
    var A := string_to_int_func(first_line[1]);
    var cards := seq(N, i requires 0 <= i < N => string_to_int_func(second_line[i]));
    var result := string_to_int_func(output[..|output|-1]);
    result == count_valid_selections(cards, A)
}

function count_valid_selections(cards: seq<int>, A: int): int
{
    var differences := seq(|cards|, i requires 0 <= i < |cards| => cards[i] - A);
    var total := count_zero_sum_subsets(differences);
    if total > 0 then total - 1 else 0
}

function count_zero_sum_subsets(differences: seq<int>): nat
{
    if |differences| == 0 then 1
    else
        var rest_count := count_zero_sum_subsets(differences[1..]);
        rest_count + count_subsets_with_sum(differences[1..], -differences[0])
}

function count_subsets_with_sum(differences: seq<int>, target: int): nat
{
    if |differences| == 0 then if target == 0 then 1 else 0
    else
        count_subsets_with_sum(differences[1..], target) +
        count_subsets_with_sum(differences[1..], target - differences[0])
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(stdin_input: string) returns (output: string)
    requires |stdin_input| > 0
    requires valid_input_format(stdin_input)
    ensures |output| > 0
    ensures output[|output|-1] == '\n'
    ensures is_valid_output(output)
    ensures output_represents_correct_count(stdin_input, output)
// </vc-spec>
// <vc-code>
{
    var lines := split_lines_func(stdin_input);
    var first_line := split_spaces_func(lines[0]);
    var N : int := string_to_int_func(first_line[0]);
    var A : int := string_to_int_func(first_line[1]);
    var second_line := split_spaces_func(lines[1]);
    var cards : seq<int> := seq(N, i requires 0 <= i < N => string_to_int_func(second_line[i]));
    var differences : seq<int> := seq(N, i requires 0 <= i < N => cards[i] - A);
    var sum_counts : map<int, nat> := map[0 := 1];
    for i : int := 0 to N-1
        invariant 0 <= i <= N
    {
        var d : int := differences[i];
        var temp_map : map<int, nat> := sum_counts;
        var add_map : map<int, nat> := map[];
        var sum_keys := set s | s in sum_counts;
        for s_val : int in sum_keys {
            var new_s : int := s_val + d;
            var add_val : nat := sum_counts[s_val];
            if new_s in add_map {
                add_map := add_map[new_s := add_map[new_s] + add_val];
            } else {
                add_map := add_map[new_s := add_val];
            }
        }
        var add_keys := set ns | ns in add_map;
        for ns : int in add_keys {
            temp_map := temp_map[ns := if ns in temp_map then temp_map[ns] + add_map[ns] else add_map[ns]];
        }
        sum_counts := temp_map;
    }
    var total : nat := if 0 in sum_counts then sum_counts[0] else 0;
    var result : int := if total > 0 then (total - 1) as int else 0;
    output := int_to_string_func(result) + "\n";
}
// </vc-code>

