// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int) -> bool {
    n > 0 && n <= 10000 && m > 1 && m <= 10
}

spec fn min_moves(n: int) -> int
    recommends n > 0
{
    if n % 2 == 0 { n / 2 } else { n / 2 + 1 }
}

spec fn valid_move_count(n: int, k: int) -> bool
    recommends n > 0
{
    min_moves(n) <= k <= n
}

spec fn is_valid_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result == -1 || (result > 0 && result % m == 0 && valid_move_count(n, result))
}

spec fn no_smaller_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result == -1 ==> forall|k: int| min_moves(n) <= k <= n ==> #[trigger] (k % m) != 0
}

spec fn is_minimal_solution(n: int, m: int, result: int) -> bool
    recommends valid_input(n, m)
{
    result != -1 ==> forall|k: int| (min_moves(n) <= k <= n && k < result) ==> #[trigger] (k % m) != 0
}
// </vc-preamble>

// <vc-helpers>
{
/* helper modified by LLM (iteration 5): min_moves bounds proof */
proof fn min_moves_bounds(n: int)
    requires n > 0
    ensures min_moves(n) >= 1, min_moves(n) <= n
{
    if n % 2 == 0 {
        assert(min_moves(n) == n / 2);
        assert(n / 2 >= 1);
        assert(n / 2 <= n);
    } else {
        assert(min_moves(n) == n / 2 + 1);
        assert(n / 2 + 1 >= 1);
        assert(n / 2 + 1 <= n);
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int)
    ensures 
        is_valid_solution(n as int, m as int, result as int) &&
        no_smaller_solution(n as int, m as int, result as int) &&
        is_minimal_solution(n as int, m as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): search for minimal multiple using i8 with safe increments and invariant tracking */
    let mut res: i8 = -1;
    let start: i8 = if n % 2 == 0 { n / 2 } else { n / 2 + 1 };
    let mut k: i8 = start;

    while k <= n
        invariant
            start as int <= k as int <= n as int,
            (res as int == -1) ==> forall|j: int| start as int <= j <= k as int - 1 ==> (j % (m as int)) != 0,
        decreases n as int - k as int + 1
    {
        if k % m == 0 {
            res = k;
            break;
        } else {
            if k == n {
                break;
            } else {
                k = k + 1;
            }
        }
    }

    res
}

// </vc-code>


}

fn main() {}