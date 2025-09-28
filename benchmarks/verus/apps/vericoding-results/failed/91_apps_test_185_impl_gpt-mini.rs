// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    2 <= n <= 5000 && 1 <= k <= n
}

spec fn optimal_moves(n: int, k: int) -> int {
    if k == 1 || k == n {
        3 * n
    } else {
        3 * n + spec_min(k - 1, n - k)
    }
}

spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute_optimal spec */
spec fn compute_optimal(n: int, k: int) -> int {
    if k == 1 || k == n {
        3 * n
    } else {
        3 * n + spec_min(k - 1, n - k)
    }
}

/* helper modified by LLM (iteration 5): proof optimal_moves_matches_compute */
proof fn optimal_moves_matches_compute(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        optimal_moves(n, k) == compute_optimal(n, k),
{
    assert(optimal_moves(n, k) == compute_optimal(n, k));
}

/* helper modified by LLM (iteration 5): proof optimal_moves_nonneg */
proof fn optimal_moves_nonneg(n: int, k: int)
    requires
        valid_input(n, k),
    ensures
        compute_optimal(n, k) >= 0,
{
    if k == 1 || k == n {
        assert(compute_optimal(n, k) == 3 * n);
        assert(3 * n >= 0);
    } else {
        assert(compute_optimal(n, k) == 3 * n + spec_min(k - 1, n - k));
        assert(k - 1 >= 0);
        assert(n - k >= 0);
        assert(spec_min(k - 1, n - k) >= 0);
        assert(3 * n + spec_min(k - 1, n - k) >= 0);
    }
}

// </vc-helpers>

// <vc-spec>
fn minimum_moves(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result as int == optimal_moves(n as int, k as int),
        result > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute using int arithmetic to avoid i8 overflow during computation */
    let n_int: int = n as int;
    let k_int: int = k as int;
    let res_int: int = if k_int == 1 || k_int == n_int {
        3 * n_int
    } else {
        3 * n_int + spec_min(k_int - 1, n_int - k_int)
    };
    proof {
        assert(valid_input(n_int, k_int));
        assert(res_int == optimal_moves(n_int, k_int));
    }
    res_int as i8
}

// </vc-code>


}

fn main() {}