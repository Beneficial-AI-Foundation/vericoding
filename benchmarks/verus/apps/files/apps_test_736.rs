// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_input(n: int, m: int) -> bool {
    n > 0 && n <= 10000 && m > 1 && m <= 10
}

spec fn min_moves(n: int) -> int {
    if n % 2 == 0 { n / 2 } else { n / 2 + 1 }
}

spec fn valid_move_count(n: int, k: int) -> bool {
    n > 0 && min_moves(n) <= k <= n
}

spec fn is_valid_solution(n: int, m: int, result: int) -> bool {
    valid_input(n, m) && (result == -1 || (result > 0 && result % m == 0 && valid_move_count(n, result)))
}

spec fn no_smaller_solution(n: int, m: int, result: int) -> bool {
    valid_input(n, m) && (result == -1 ==> forall|k: int| (min_moves(n) <= k <= n) ==> k % m != 0)
}

spec fn is_minimal_solution(n: int, m: int, result: int) -> bool {
    valid_input(n, m) && (result != -1 ==> forall|k: int| (min_moves(n) <= k <= n && k < result) ==> k % m != 0)
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int, m: int) -> (result: int)
    requires 
        valid_input(n, m)
    ensures 
        is_valid_solution(n, m, result) &&
        no_smaller_solution(n, m, result) &&
        is_minimal_solution(n, m, result)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}