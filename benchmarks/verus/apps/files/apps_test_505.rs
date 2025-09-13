// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int, k: int, grid: Seq<Seq<char>>) -> bool {
    n > 0 && m > 0 && k >= 0 &&
    grid.len() == n &&
    (forall|i: int| 0 <= i < n ==> grid[i].len() == m) &&
    (exists|i: int, j: int| 0 <= i < n && 0 <= j < m && grid[i][j] == 'X') &&
    (forall|i: int| 0 <= i < n ==> forall|c: char| grid[i].contains(c) ==> c == '.' || c == '*' || c == 'X') &&
    (set![|i: int, j: int| 0 <= i < n && 0 <= j < m && grid[i][j] == 'X'].len() == 1)
}

spec fn get_next_position(x: int, y: int, move_char: char) -> (int, int) {
    match move_char {
        'D' => (x + 1, y),
        'L' => (x, y - 1),
        'R' => (x, y + 1),
        'U' => (x - 1, y),
        _ => (x, y),
    }
}

spec fn simulate_path(start_x: int, start_y: int, path: Seq<char>, grid: Seq<Seq<char>>, n: int, m: int) -> (int, int)
    decreases path.len()
{
    if path.len() == 0 {
        (start_x, start_y)
    } else {
        let next_pos = get_next_position(start_x, start_y, path[0]);
        simulate_path(next_pos.0, next_pos.1, path.subrange(1, path.len() as int), grid, n, m)
    }
}

spec fn valid_path(start_x: int, start_y: int, path: Seq<char>, grid: Seq<Seq<char>>, n: int, m: int) -> bool {
    forall|i: int| 0 <= i <= path.len() ==> {
        let pos = simulate_path(start_x, start_y, path.subrange(0, i), grid, n, m);
        0 <= pos.0 < n && 0 <= pos.1 < m && 
        pos.0 < grid.len() && pos.1 < grid[pos.0].len() &&
        grid[pos.0][pos.1] != '*'
    }
}

spec fn path_returns_to_start(start_x: int, start_y: int, path: Seq<char>, grid: Seq<Seq<char>>, n: int, m: int) -> bool {
    let final_pos = simulate_path(start_x, start_y, path, grid, n, m);
    final_pos.0 == start_x && final_pos.1 == start_y
}

spec fn valid_directions(path: Seq<char>) -> bool {
    forall|c: char| path.contains(c) ==> c == 'D' || c == 'L' || c == 'R' || c == 'U'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int, k: int, grid: Seq<Seq<char>>) -> (result: Seq<char>)
    requires valid_input(n, m, k, grid)
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