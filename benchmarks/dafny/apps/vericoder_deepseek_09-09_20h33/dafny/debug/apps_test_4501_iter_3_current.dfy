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
predicate is_valid_integer(s: string) {
    |s| > 0 && (s[0] == '-' && |s| > 1 ==> (forall i | 1 <= i < |s| :: '0' <= s[i] <= '9')) &&
    (s[0] != '-' ==> (forall i | 0 <= i < |s| :: '0' <= s[i] <= '9'))
}

function string_to_int_func(s: string): int
    requires is_valid_integer(s)
{
    if |s| == 0 then 0
    else if s[0] == '-' then -string_to_nat(s[1..])
    else string_to_nat(s)
}

function string_to_nat(s: string): nat
    requires forall i | 0 <= i < |s| :: '0' <= s[i] <= '9'
{
    if |s| == 0 then 0
    else (s[0] as int - '0' as int) * pow10(|s| - 1) + string_to_nat(s[1..])
}

function pow10(n: nat): nat {
    if n == 0 then 1
    else 10 * pow10(n - 1)
}

function split_lines_func(s: string): seq<string> {
    if |s| == 0 then []
    else
        var idx := find_newline(s, 0);
        if idx == -1 then [s]
        else [s[..idx]] + split_lines_func(s[idx+1..])
}

function find_newline(s: string, start: nat): int
    requires start <= |s|
{
    if start >= |s| then -1
    else if s[start] == '\n' then start
    else find_newline(s, start + 1)
}

function split_spaces_func(s: string): seq<string> {
    if |s| == 0 then []
    else
        var start := find_non_space(s, 0);
        if start == -1 then []
        else
            var end := find_space(s, start);
            if end == -1 then [s[start..]]
            else [s[start..end]] + split_spaces_func(s[end..])
}

function find_non_space(s: string, start: nat): int
    requires start <= |s|
{
    if start >= |s| then -1
    else if s[start] != ' ' then start
    else find_non_space(s, start + 1)
}

function find_space(s: string, start: nat): int
    requires start <= |s|
{
    if start >= |s| then -1
    else if s[start] == ' ' then start
    else find_space(s, start + 1)
}

function int_to_string_func(n: int): string {
    if n < 0 then "-" + nat_to_string(-n as nat)
    else nat_to_string(n as nat)
}

function nat_to_string(n: nat): string {
    if n < 10 then [digit_to_char(n)]
    else nat_to_string(n / 10) + [digit_to_char(n % 10)]
}

function digit_to_char(d: nat): char
    requires d < 10
{
    ('0' as int + d) as char
}

lemma count_subsets_with_sum_properties(differences: seq<int>, target: int)
    ensures count_subsets_with_sum(differences, target) >= 0
{
}

lemma count_zero_sum_subsets_properties(differences: seq<int>)
    ensures count_zero_sum_subsets(differences) >= 0
{
}

lemma count_valid_selections_properties(cards: seq<int>, A: int)
    ensures count_valid_selections(cards, A) >= 0
{
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
    var second_line := split_spaces_func(lines[1]);
    var N_str := first_line[0];
    var A_str := first_line[1];
    assert is_valid_integer(N_str);
    assert is_valid_integer(A_str);
    var N := string_to_int_func(N_str);
    var A := string_to_int_func(A_str);
    
    var cards: seq<int> := [];
    var i: nat := 0;
    while i < |second_line|
        invariant 0 <= i <= |second_line|
        invariant |cards| == i
        invariant forall k | 0 <= k < i :: is_valid_integer(second_line[k])
    {
        var num_str := second_line[i];
        assert is_valid_integer(num_str);
        var num := string_to_int_func(num_str);
        cards := cards + [num];
        i := i + 1;
    }
    
    var count := count_valid_selections(cards, A);
    output := int_to_string_func(count) + "\n";
}
// </vc-code>

