// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn solve_maze_path_spec(n: nat, m: nat) -> bool
{
    (n == 1 && m == 2) || (n == 2 && m == 1) || 
    (n > 1 && m > 1 && (n * m) % 2 == 0)
}

fn solve_maze_path(n: nat, m: nat) -> (result: &'static str)
    requires n > 0, m > 0,
    ensures 
        result == "Yes" || result == "No",
        result == "Yes" <==> solve_maze_path_spec(n, m)
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

fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // assert(solve_maze_path(2, 2) == "Yes");
    // assert(solve_maze_path(2, 3) == "Yes");
    // assert(solve_maze_path(1, 3) == "No");
}