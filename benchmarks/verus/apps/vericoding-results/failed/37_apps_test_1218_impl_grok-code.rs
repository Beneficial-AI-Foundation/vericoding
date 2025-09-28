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
/* helpers modified by LLM (iteration 5): No changes needed, kept empty */

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
    /* code modified by LLM (iteration 5): Used i64 for computations to prevent arithmetic overflow */
    let nn: i64 = n as i64;
    let kk: i64 = k as i64;
    let c: i64 = 2 * (nn - 1) - kk * (kk - 1);
    if c > 0 {
        return -1;
    }
    let mut x: i64 = 0;
    while x <= kk
        invariant
            x >= 0,
            x <= kk + 1,
        decreases (kk - x) as nat
    {
        let quadratic_val: i64 = x * x - x + c;
        let next_quadratic_val: i64 = if x == 0 { 1 } else { (x + 1) * (x + 1) - (x + 1) + c };
        let quad = quadratic_val <= 0;
        let next_quad = x == 0 || next_quadratic_val > 0;
        if quad && next_quad {
            return (kk - x) as i8;
        }
        x = x + 1;
    }
    return -1;
}

// </vc-code>


}

fn main() {}