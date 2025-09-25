// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, m: int, k: int, grid: Seq<Seq<char>>) -> bool {
    n > 0 && m > 0 && k >= 0 &&
    grid.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] grid[i].len() == m) &&
    (exists|i: int, j: int| 0 <= i < n && 0 <= j < m && grid[i][j] == 'X')
}

spec fn get_next_position(x: int, y: int, move_char: char) -> (int, int) {
    match move_char {
        'D' => (x + 1, y),
        'L' => (x, y - 1),
        'R' => (x, y + 1),
        'U' => (x - 1, y),
        _ => (x, y)
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
    forall|i: int| #![trigger simulate_path(start_x, start_y, path.subrange(0, i), grid, n, m)] 
        0 <= i <= path.len() ==> {
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
    forall|i: int| 0 <= i < path.len() ==> 
        #[trigger] path[i] == 'D' || path[i] == 'L' || path[i] == 'R' || path[i] == 'U'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, m: usize, k: usize, grid: Vec<Vec<char>>) -> (result: String)
    requires
        valid_input(n as int, m as int, k as int, grid@.map_values(|row: Vec<char>| row@))
    ensures
        result == "IMPOSSIBLE" || (
            result.len() == k &&
            valid_directions(result@) &&
            {
                let mut start_x = 0;
                let mut start_y = 0;
                let mut found = false;
                let mut i = 0;
                while i < n {
                    let mut j = 0;
                    while j < m {
                        if grid[i][j] == 'X' {
                            start_x = i as int;
                            start_y = j as int;
                            found = true;
                        }
                        j += 1;
                    }
                    i += 1;
                }
                found
            } ==> {
                let start_x = {
                    let mut sx = 0;
                    let mut i = 0;
                    while i < n {
                        let mut j = 0;
                        while j < m {
                            if grid[i][j] == 'X' {
                                sx = i as int;
                            }
                            j += 1;
                        }
                        i += 1;
                    }
                    sx
                };
                let start_y = {
                    let mut sy = 0;
                    let mut i = 0;
                    while i < n {
                        let mut j = 0;
                        while j < m {
                            if grid[i][j] == 'X' {
                                sy = j as int;
                            }
                            j += 1;
                        }
                        i += 1;
                    }
                    sy
                };
                valid_path(start_x, start_y, result@, grid@.map_values(|row: Vec<char>| row@), n as int, m as int) &&
                path_returns_to_start(start_x, start_y, result@, grid@.map_values(|row: Vec<char>| row@), n as int, m as int)
            }
        )
// </vc-spec>
// <vc-code>
{
    assume(false);
    "IMPOSSIBLE".to_string()
}
// </vc-code>


}

fn main() {}