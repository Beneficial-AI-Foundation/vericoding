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
function char_to_digit(c: char): int
    requires '0' <= c <= '9'
    ensures 0 <= char_to_digit(c) <= 9
{
    (c as int) - ('0' as int)
}

function string_to_int_func(s: string): int
    requires forall i | 0 <= i < |s| :: '0' <= s[i] <= '9'
    decreases |s|
{
    if |s| == 0 then 0
    else char_to_digit(s[|s|-1]) + 10 * string_to_int_func(s[..|s|-1])
}

function is_valid_integer(s: string): bool
{
    |s| > 0 && forall i | 0 <= i < |s| :: '0' <= s[i] <= '9'
}

function int_to_string_func(i: int): string
{
    if i == 0 then "0"
    else abs(i).ToString()  // using ToString, assuming Dafny has it or define recursive
}

function find_index_of_char(s: string, c: char, idx: nat): nat
    requires idx <= |s|
    decreases |s| - idx
{
    if idx == |s| then |s|
    else if s[idx] == c then idx
    else find_index_of_char(s, c, idx + 1)
}

function split_by_char(s: string, c: char): seq<string>
    decreases |s|
{
    if |s| == 0 then []
    else 
        var idx := find_index_of_char(s, c, 0);
        if idx == 0 then 
            if |s| > 0 && s[0] == c then [s[0..0]] + split_by_char(s[1..], c)
            else split_by_char(s[1..], c)
        else 
            [s[0..idx]] + split_by_char(s[idx + 1..], c)
}

function split_lines_func(s: string): seq<string>
{
    split_by_char(s, '\n')
}

function split_spaces_func(s: string): seq<string>
{
    split_by_char(s, ' ')
}
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
        for s := -2500 to 2500
            invariant temp_map.Keys <= sum_counts.Keys + (set k | -2500 <= k <= 2500)
        {
            if s in sum_counts {
                var add_val := sum_counts[s];
                if s + d in temp_map {
                    temp_map := temp_map[s + d := temp_map[s + d] + add_val];
                } else {
                    temp_map := temp_map[s + d := add_val];
                }
            }
        }
        sum_counts := temp_map;
    }
    var total : nat := if 0 in sum_counts then sum_counts[0] else 0;
    var result : int := if total > 0 then (total - 1) as int else 0;
    output := int_to_string_func(result) + "\n";
}
// </vc-code>

