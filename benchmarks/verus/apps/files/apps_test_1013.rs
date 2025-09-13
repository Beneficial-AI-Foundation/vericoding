// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Helper functions for string operations */
spec fn split_lines_func(input: &str) -> Seq<&str>;
spec fn split_whitespace_func(input: &str) -> Seq<&str>;
spec fn string_to_int_func(input: &str) -> int;

spec fn valid_input(input: &str) -> bool {
    let lines = split_lines_func(input);
    lines.len() >= 2 &&
    {let first_line = lines[0];
    let nm_parts = split_whitespace_func(first_line);
    nm_parts.len() >= 2 &&
    {let n = string_to_int_func(nm_parts[0]);
    let m = string_to_int_func(nm_parts[1]);
    n >= 3 && m >= 3 &&
    lines.len() >= n + 1 &&
    (forall|i: int| 1 <= i <= n ==> 
        {let row_parts = split_whitespace_func(lines[i]);
        row_parts.len() >= m &&
        (forall|j: int| 0 <= j < m ==> row_parts[j] == "0" || row_parts[j] == "1")}) &&
    (exists|i: int, j: int| 0 <= i < n && 0 <= j < m && get_grid_cell_helper(lines, i, j) == "1") &&
    get_grid_cell_helper(lines, 0, 0) == "0" &&
    get_grid_cell_helper(lines, 0, m-1) == "0" &&
    get_grid_cell_helper(lines, n-1, 0) == "0" &&
    get_grid_cell_helper(lines, n-1, m-1) == "0"}}
}

spec fn get_grid_cell_helper(lines: Seq<&str>, i: int, j: int) -> &str {
    let line = lines[i + 1];
    let parts = split_whitespace_func(line);
    if j < parts.len() { parts[j] } else { "0" }
}

spec fn get_n(input: &str) -> int {
    let lines = split_lines_func(input);
    let first_line = lines[0];
    let parts = split_whitespace_func(first_line);
    string_to_int_func(parts[0])
}

spec fn get_m(input: &str) -> int {
    let lines = split_lines_func(input);
    let first_line = lines[0];
    let parts = split_whitespace_func(first_line);
    string_to_int_func(parts[1])
}

spec fn get_grid_cell(input: &str, i: int, j: int) -> &str {
    let lines = split_lines_func(input);
    let line = lines[i + 1];
    let parts = split_whitespace_func(line);
    parts[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: &str) -> (result: String)
    requires 
        input.len() > 0,
        valid_input(input),
    ensures
        result.view() == seq!['2', '\n'] || result.view() == seq!['4', '\n'],
        result.view() == seq!['2', '\n'] <==> (exists|i: int, j: int| 0 <= i < get_n(input) && 0 <= j < get_m(input) && 
                             get_grid_cell(input, i, j) == "1" && 
                             (i == 0 || j == 0 || i == get_n(input) - 1 || j == get_m(input) - 1)),
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