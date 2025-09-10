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
function {:axiom} split_lines_func(s: string): seq<string>

function {:axiom} split_spaces_func(s: string): seq<string>

function {:axiom} is_valid_integer(s: string): bool

function {:axiom} string_to_int_func(s: string): int
    requires is_valid_integer(s)

function {:axiom} int_to_string_func(n: int): string
    ensures is_valid_integer(int_to_string_func(n))
    ensures string_to_int_func(int_to_string_func(n)) == n
    ensures |int_to_string_func(n)| >= 1

method {:axiom} split_lines(s: string) returns (lines: seq<string>)
    ensures lines == split_lines_func(s)

method {:axiom} split_spaces(s: string) returns (tokens: seq<string>)
    ensures tokens == split_spaces_func(s)

method {:axiom} string_to_int(s: string) returns (n: int)
    requires is_valid_integer(s)
    ensures n == string_to_int_func(s)

method {:axiom} int_to_string(n: int) returns (s: string)
    ensures s == int_to_string_func(n)
    ensures is_valid_integer(s)
    ensures string_to_int_func(s) == n
    ensures |s| >= 1

method count_zero_sum_subsets_impl(differences: seq<int>) returns (count: nat)
    ensures count == count_zero_sum_subsets(differences)
{
    if |differences| == 0 {
        return 1;
    }
    var rest_count := count_zero_sum_subsets_impl(differences[1..]);
    var with_first := count_subsets_with_sum_impl(differences[1..], -differences[0]);
    return rest_count + with_first;
}

method count_subsets_with_sum_impl(differences: seq<int>, target: int) returns (count: nat)
    ensures count == count_subsets_with_sum(differences, target)
{
    if |differences| == 0 {
        if target == 0 {
            return 1;
        } else {
            return 0;
        }
    }
    var without := count_subsets_with_sum_impl(differences[1..], target);
    var with := count_subsets_with_sum_impl(differences[1..], target - differences[0]);
    return without + with;
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
    var lines := split_lines(stdin_input);
    var first_line := split_spaces(lines[0]);
    var second_line := split_spaces(lines[1]);
    
    var N := string_to_int(first_line[0]);
    var A := string_to_int(first_line[1]);
    
    var cards := new int[N];
    var i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant forall j | 0 <= j < i :: cards[j] == string_to_int_func(second_line[j])
    {
        cards[i] := string_to_int(second_line[i]);
        i := i + 1;
    }
    
    var cards_seq := cards[..];
    assert cards_seq == seq(N, j requires 0 <= j < N => string_to_int_func(second_line[j]));
    
    var differences := new int[N];
    i := 0;
    while i < N
        invariant 0 <= i <= N
        invariant forall j | 0 <= j < i :: differences[j] == cards_seq[j] - A
    {
        differences[i] := cards_seq[i] - A;
        i := i + 1;
    }
    
    var differences_seq := differences[..];
    assert differences_seq == seq(|cards_seq|, j requires 0 <= j < |cards_seq| => cards_seq[j] - A);
    
    var total := count_zero_sum_subsets_impl(differences_seq);
    var result := if total > 0 then total - 1 else 0;
    
    assert result == count_valid_selections(cards_seq, A);
    
    var result_str := int_to_string(result);
    output := result_str + "\n";
}
// </vc-code>

