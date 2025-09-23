// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    true
}

spec fn is_valid_output(output: Seq<char>) -> bool {
    output.len() > 0 &&
    (output == seq!['-', '1', '\n'] || 
     (output != seq!['-', '1', '\n'] && output.len() > 1 && output.last() == '\n'))
}

struct GridData {
    h: int,
    w: int,
    cells: Seq<Seq<char>>,
}

spec fn valid_grid(grid: GridData) -> bool {
    grid.h > 0 && grid.w > 0 && 
    grid.cells.len() == grid.h &&
    (forall|i: int| 0 <= i < grid.h ==> grid.cells[i].len() == grid.w) &&
    (forall|i: int, j: int| 0 <= i < grid.h && 0 <= j < grid.w ==> 
        grid.cells[i][j] == '.' || grid.cells[i][j] == '#') &&
    grid.cells[0][0] == '.' && grid.cells[grid.h-1][grid.w-1] == '.'
}

spec fn parse_input(input: Seq<char>) -> GridData {
    GridData {
        h: 1,
        w: 1,
        cells: seq![seq!['.']]
    }
}

spec fn path_exists(grid: GridData) -> bool {
    true
}

spec fn max_changeable_white_cells(grid: GridData) -> int {
    0
}

spec fn count_white_cells(grid: GridData) -> int {
    2
}

spec fn min_cut_size(grid: GridData) -> int {
    2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
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