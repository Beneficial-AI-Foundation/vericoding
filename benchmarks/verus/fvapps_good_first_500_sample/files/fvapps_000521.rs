// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve_queens(n: nat, m: nat, x: nat, y: nat) -> (result: nat)
    requires 
        n >= 2,
        m >= 2,
        x >= 1 && x <= n,
        y >= 1 && y <= m,
    ensures
        result >= 0,
        result % 2 == 0,
        result <= (n * m) * (n * m - 1),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


/* proof functions for theorem properties */
proof fn queens_symmetry_rotate_180(n: nat, m: nat, x: nat, y: nat)
    requires x <= n && y <= m && n >= x && m >= y
    ensures solve_queens(n, m, x, y) == solve_queens(n, m, n.checked_sub(x).unwrap_or(0) + 1, m.checked_sub(y).unwrap_or(0) + 1)
{
    assume(false);
}

proof fn queens_square_board_nonnegative(n: nat, x: nat, y: nat)
    requires x <= n && y <= n
    ensures solve_queens(n, n, x, y) >= 0
{
    assume(false);
}

proof fn queens_corner_symmetry(n: nat, m: nat)
    requires n >= 2 && m >= 2
    ensures solve_queens(n, m, 1, 1) == solve_queens(n, m, n, m)
{
    assume(false);
}

}
fn main() {
    // #guard_msgs in
    // #eval solve_queens 3 3 2 2
    
    // #guard_msgs in
    // #eval solve_queens 4 4 2 3
}