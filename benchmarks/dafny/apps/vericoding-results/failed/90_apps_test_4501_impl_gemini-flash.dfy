// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed a compilation error by adding proper type annotations to `N_out` and `A_out` in the `CalculateNAndA` function signature. */
function CalculateNAndA(stdin_input: string) : (N_out: int, A_out: int)
{
  var lines := split_lines_func(stdin_input);
  var first_line := split_spaces_func(lines[0]);
  (string_to_int_func(first_line[0]), string_to_int_func(first_line[1]))
}

/* helper modified by LLM (iteration 4): Added a helper function to extract the sequence of cards from the input string. */
function GetCards(stdin_input: string, N: int): seq<int>
{
    var lines := split_lines_func(stdin_input);
    var second_line := split_spaces_func(lines[1]);
    seq(N, i requires 0 <= i < N => string_to_int_func(second_line[i]))
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
/* code modified by LLM (iteration 5): Resolved the compilation error in the helper function `CalculateNAndA` and retained the logic for calculating N, A, cards, and the final count. */
{
  var N_val: int, A_val: int := CalculateNAndA(stdin_input);
  var cards: seq<int> := GetCards(stdin_input, N_val);
  var count: int := count_valid_selections(cards, A_val);
  output := int_to_string_func(count) + "\n";
}
// </vc-code>
