// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 2
}

spec fn impossibility_condition(n: int, k: int) -> bool
    recommends valid_input(n, k)
{
    2 * (n - 1) - k * (k - 1) > 0
}

spec fn quadratic_condition(x: int, n: int, k: int) -> bool {
    x * x - x + (2 * (n - 1) - k * (k - 1)) <= 0
}

spec fn next_quadratic_condition(x: int, n: int, k: int) -> bool {
    (x + 1) * (x + 1) - (x + 1) + (2 * (n - 1) - k * (k - 1)) > 0
}

spec fn valid_solution(n: int, k: int, result: int) -> bool
    recommends valid_input(n, k)
{
    if impossibility_condition(n, k) {
        result == -1
    } else {
        result >= 0 && result <= k &&
        exists|x: int| #[trigger] quadratic_condition(x, n, k) &&
            x >= 0 && 
            quadratic_condition(x, n, k) && 
            (x == 0 || next_quadratic_condition(x, n, k)) &&
            result == k - x
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed proof blocks from specs, fixed type conversions */
proof fn lemma_quadratic_condition_exists(n: int, k: int) 
    requires
        valid_input(n, k),
        !impossibility_condition(n, k)
    ensures
        exists|x: int| #[trigger] quadratic_condition(x, n, k) && x >= 0
{
    assert(quadratic_condition(0, n, k));
}

proof fn lemma_next_quadratic_condition_unique(n: int, k: int, x: int) 
    requires
        valid_input(n, k),
        !impossibility_condition(n, k),
        quadratic_condition(x, n, k),
        x >= 0
    ensures
        x == 0 || next_quadratic_condition(x, n, k)
{
    if x > 0 {
        assert(next_quadratic_condition(x, n, k));
    }
}

spec fn as_int_to_int(i: i8) -> int { i as int }
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result >= -1,
        (result == -1) <==> impossibility_condition(n as int, k as int),
        valid_solution(n as int, k as int, result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariant and proof block usage */
    if impossibility_condition(n as int, k as int) {
        -1
    } else {
        proof {
            lemma_quadratic_condition_exists(n as int, k as int);
        }
        let mut x: i8 = 0;
        while x <= k
            invariant
                x >= 0,
                quadratic_condition(x as int, n as int, k as int)
        {
            x = x + 1;
            if !quadratic_condition(x as int, n as int, k as int) {
                break;
            }
        }
        x = x - 1;
        proof {
            lemma_next_quadratic_condition_unique(n as int, k as int, x as int);
        }
        k - x
    }
}
// </vc-code>


}

fn main() {}