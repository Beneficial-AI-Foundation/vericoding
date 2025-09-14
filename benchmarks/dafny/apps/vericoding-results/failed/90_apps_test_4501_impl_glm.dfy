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
function split_lines_func(s: string): seq<string>
{
    if s == "" then []
    else
        var i := 0;
        while (i < |s| && s[i] != '\n')
            invariant 0 <= i <= |s|
        {
            i := i + 1;
        }
        if i == |s| then [s]
        else [s[..i]] + split_lines_func(s[i+1..])
}

function split_spaces_func(s: string): seq<string>
{
    if s == "" then []
    else
        var i := 0;
        while (i < |s| && s[i] != ' ')
            invariant 0 <= i <= |s|
        {
            i := i + 1;
        }
        if i == |s| then [s]
        else [s[..i]] + split_spaces_func(s[i+1..])
}

predicate is_valid_integer(s: string)
{
    s != "" &&
    let start := if s[0] == '-' then 1 else 0 in
        start < |s| &&
        forall j | start <= j < |s| :: '0' <= s[j] <= '9'
}

function string_to_int_func(s: string): int
    requires is_valid_integer(s)
{
    if s == "" then 0
    else
        var i := 0;
        var sign := 1;
        if s[0] == '-' {
            sign := -1;
            i := 1;
        }
        var result := 0;
        while (i < |s|)
            invariant 0 <= i <= |s|
            invariant result >= 0
        {
            result := result * 10 + (s[i] - '0');
            i := i + 1;
        }
        sign * result
}

function int_to_string_func(n: int): string
{
    if n == 0 then "0"
    else
        var sign := if n < 0 then -1 else 1;
        var num := if n < 0 then -n else n;
        var s := "";
        while (num != 0)
            invariant num >= 0
            decreases num
        {
            var digit := num % 10;
            s := ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"][digit] + s;
            num := num / 10;
        }
        if sign == -1 then "-" + s else s
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
  var N := string_to_int_func(first_line[0]);
  var A := string_to_int_func(first_line[1]);
  var cards := seq(N, i requires 0 <= i < N => string_to_int_func(second_line[i]));
  var result := count_valid_selections(cards, A);
  output := int_to_string_func(result) + "\n";
}
// </vc-code>

