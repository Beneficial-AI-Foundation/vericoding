// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn split_lines_func(input: Seq<char>) -> Seq<Seq<char>>
{
    Seq::empty()
}

spec fn split_spaces_func(line: Seq<char>) -> Seq<Seq<char>>
{
    Seq::empty()
}

spec fn is_valid_integer(s: Seq<char>) -> bool
{
    true
}

spec fn string_to_int_func(s: Seq<char>) -> int
{
    0
}

spec fn valid_input_format(stdin_input: Seq<char>) -> bool {
    let lines = split_lines_func(stdin_input);
    lines.len() >= 2 &&
    {
        let first_line = split_spaces_func(lines[0]);
        let second_line = split_spaces_func(lines[1]);
        first_line.len() == 2 &&
        is_valid_integer(first_line[0]) &&
        is_valid_integer(first_line[1]) &&
        {
            let N = string_to_int_func(first_line[0]);
            let A = string_to_int_func(first_line[1]);
            1 <= N <= 50 &&
            1 <= A <= 50 &&
            second_line.len() == N &&
            (forall|j: int| 0 <= j < second_line.len() ==> 
                is_valid_integer(second_line[j]) &&
                1 <= string_to_int_func(second_line[j]) <= 50)
        }
    }
}

spec fn is_valid_output(output: Seq<char>) -> bool {
    output.len() > 1 && 
    output[output.len() as int - 1] == '\n' &&
    {
        let result_str = output.subrange(0, output.len() as int - 1);
        is_valid_integer(result_str) &&
        string_to_int_func(result_str) >= 0
    }
}

spec fn output_represents_correct_count(stdin_input: Seq<char>, output: Seq<char>) -> bool
    recommends
        valid_input_format(stdin_input),
        is_valid_output(output)
{
    let lines = split_lines_func(stdin_input);
    let first_line = split_spaces_func(lines[0]);
    let second_line = split_spaces_func(lines[1]);
    let N = string_to_int_func(first_line[0]);
    let A = string_to_int_func(first_line[1]);
    let cards = Seq::new(N as nat, |i: int| string_to_int_func(second_line[i]));
    let result = string_to_int_func(output.subrange(0, output.len() as int - 1));
    result == count_valid_selections(cards, A)
}

spec fn count_valid_selections(cards: Seq<int>, A: int) -> int {
    let differences = Seq::new(cards.len(), |i: int| cards[i] - A);
    let total = count_zero_sum_subsets(differences);
    if total > 0 { total - 1 } else { 0 }
}

spec fn count_zero_sum_subsets(differences: Seq<int>) -> nat
    decreases differences.len()
{
    if differences.len() == 0 {
        1
    } else {
        let rest_count = count_zero_sum_subsets(differences.subrange(1, differences.len() as int));
        rest_count + count_subsets_with_sum(differences.subrange(1, differences.len() as int), -differences[0])
    }
}

spec fn count_subsets_with_sum(differences: Seq<int>, target: int) -> nat
    decreases differences.len()
{
    if differences.len() == 0 {
        if target == 0 { 1 } else { 0 }
    } else {
        count_subsets_with_sum(differences.subrange(1, differences.len() as int), target) +
        count_subsets_with_sum(differences.subrange(1, differences.len() as int), target - differences[0])
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
    requires
        stdin_input@.len() > 0,
        valid_input_format(stdin_input@),
    ensures
        output@.len() > 0,
        output@[output@.len() as int - 1] == '\n',
        is_valid_output(output@),
        output_represents_correct_count(stdin_input@, output@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {}