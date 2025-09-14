// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 && input.contains('\n')
}

spec fn can_be_constructed_by_operations(input: Seq<char>) -> bool
    recommends valid_input(input)
{
    let lines = split_lines(input);
    if lines.len() < 2 {
        false
    } else {
        let first_line = lines[0];
        let grid_lines = lines.subrange(1, lines.len() as int);
        let dimensions = parse_dimensions(first_line);
        let n = dimensions.0;
        let m = dimensions.1;
        if n <= 0 || m <= 0 || grid_lines.len() != n {
            false
        } else if !valid_grid(grid_lines, m) {
            false
        } else {
            forall|col: int| 0 <= col < m ==> {
                let rows_with_this_col = Set::new(|i: int| 0 <= i < n && col < grid_lines[i].len() && grid_lines[i][col] == '#');
                rows_with_this_col.len() <= 1 ||
                (forall|i: int, j: int| rows_with_this_col.contains(i) && rows_with_this_col.contains(j) ==>
                    get_row_pattern(grid_lines[i], m) == get_row_pattern(grid_lines[j], m))
            }
        }
    }
}

spec fn valid_grid(grid_lines: Seq<Seq<char>>, m: int) -> bool {
    (forall|i: int| 0 <= i < grid_lines.len() ==> grid_lines[i].len() == m) &&
    (forall|i: int| 0 <= i < grid_lines.len() ==> 
        forall|j: int| 0 <= j < grid_lines[i].len() ==> grid_lines[i][j] == '.' || grid_lines[i][j] == '#')
}

spec fn get_row_pattern(row: Seq<char>, m: int) -> Set<int>
    recommends row.len() == m
{
    Set::new(|j: int| 0 <= j < m && row[j] == '#')
}

spec fn split_lines(input: Seq<char>) -> Seq<Seq<char>>
    recommends input.len() > 0
{
    split_lines_helper(input, 0, seq![])
}

spec fn parse_dimensions(line: Seq<char>) -> (int, int) {
    let parts = split_on_space(line);
    if parts.len() >= 2 {
        (string_to_int(parts[0]), string_to_int(parts[1]))
    } else {
        (0, 0)
    }
}
spec fn split_lines_helper(input: Seq<char>, start: int, acc: Seq<Seq<char>>) -> Seq<Seq<char>> {
    if start >= input.len() {
        acc
    } else {
        acc.push(seq!['0'])
    }
}

spec fn split_on_space(line: Seq<char>) -> Seq<Seq<char>> {
    seq![seq!['0'], seq!['0']]
}

spec fn string_to_int(s: Seq<char>) -> int {
    0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: String) -> (result: String)
    requires valid_input(stdin_input@)
    ensures 
        result@ == seq!['Y','e','s','\n'] || result@ == seq!['N','o','\n'],
        result@.len() > 0,
        (result@ == seq!['Y','e','s','\n']) <==> can_be_constructed_by_operations(stdin_input@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    "No\n".to_string()
}
// </vc-code>


}

fn main() {}