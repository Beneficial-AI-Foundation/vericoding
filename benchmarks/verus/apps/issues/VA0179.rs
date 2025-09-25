// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn parse_input_lines(input: Seq<char>) -> Seq<Seq<char>>
{
    split_by_newline_simple(input, 0, seq![])
}

spec fn split_by_newline_simple(input: Seq<char>, pos: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases input.len() - pos
{
    if pos >= input.len() {
        acc
    } else {
        let next_newline = find_next_newline(input, pos);
        if next_newline == -1 {
            if pos < input.len() {
                acc.push(input.subrange(pos, input.len() as int))
            } else {
                acc
            }
        } else {
            split_by_newline_simple(input, next_newline + 1, acc.push(input.subrange(pos, next_newline)))
        }
    }
}

spec fn find_next_newline(input: Seq<char>, start: int) -> int
    decreases input.len() - start
{
    if start >= input.len() {
        -1
    } else if input[start] == '\n' {
        start
    } else {
        find_next_newline(input, start + 1)
    }
}

spec fn count_black_in_square(lines: Seq<Seq<char>>, row: int, col: int) -> int
{
    (if lines[row][col] == '#' { 1int } else { 0int }) +
    (if lines[row][col + 1] == '#' { 1int } else { 0int }) +
    (if lines[row + 1][col] == '#' { 1int } else { 0int }) +
    (if lines[row + 1][col + 1] == '#' { 1int } else { 0int })
}

spec fn valid_grid(lines: Seq<Seq<char>>) -> bool
{
    lines.len() == 4 && (forall|k: int| 0 <= k < 4 ==> lines[k].len() >= 4)
}

spec fn can_make_uniform_square(lines: Seq<Seq<char>>) -> bool
{
    exists|i: int, j: int| 0 <= i <= 2 && 0 <= j <= 2 && 
        i + 1 < lines.len() && j + 1 < lines[i].len() && j + 1 < lines[i + 1].len() &&
        {
            let black_count = count_black_in_square(lines, i, j);
            black_count >= 3 || black_count <= 1
        }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires input.len() > 0
    ensures result@ =~= seq!['Y', 'E', 'S'] || result@ =~= seq!['N', 'O']
// </vc-spec>
// <vc-code>
{
    assume(false);
    String::new()
}
// </vc-code>


}

fn main() {}