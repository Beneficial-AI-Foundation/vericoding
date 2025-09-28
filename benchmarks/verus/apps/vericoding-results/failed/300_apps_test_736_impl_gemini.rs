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
/* helper modified by LLM (iteration 4): re-validated helper, no change in logic */
fn compute_min_moves(n: i8) -> (result: i8)
    requires
        n > 0,
    ensures
        result > 0,
        result as int == min_moves(n as int),
{
    if n % 2 == 0 {
        n / 2
    } else {
        n / 2 + 1
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
/* code modified by LLM (iteration 4): added a precise trigger to the forall in loop invariant */
{
    let ghost n_int = n as int;
    let ghost m_int = m as int;

    let min_k = compute_min_moves(n);
    
    let mut k: i32 = min_k as i32;
    let n_i32 = n as i32;
    let m_i32 = m as i32;

    while k <= n_i32
        invariant
            min_moves(n_int) <= k as int,
            k as int <= n_int + 1,
            forall|j: int| min_moves(n_int) <= j < k as int ==> (#[trigger] (j % m_int)) != 0,
        decreases n_i32 - k
    {
        if k % m_i32 == 0 {
            return k as i8;
        }
        k = k + 1;
    }

    -1
}
// </vc-code>


}

fn main() {}