// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int) -> bool {
    n >= 1 && k >= 2
}

spec fn satisfies_constraint(x: int, n: int, k: int) -> bool {
    x > 0 && k > 0 && (x / k) * (x % k) == n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed int type usage by using i32 for computation */
fn compute_minimal_x(n: i8, k: i8) -> (x: i8)
    requires valid_input(n as int, k as int)
    ensures 
        satisfies_constraint(x as int, n as int, k as int),
        forall|y: int| #[trigger] satisfies_constraint(y, n as int, k as int) ==> x as int <= y
{
    let n_i32 = n as i32;
    let k_i32 = k as i32;
    let mut min_x_i32 = n_i32 * k_i32 + 1_i32;
    let mut r_i32 = 2_i32;

    while r_i32 < k_i32
        invariant 
            2 <= (r_i32 as int) <= (k_i32 as int),
            min_x_i32 > 0,
            satisfies_constraint(min_x_i32 as int, n as int, k as int),
            forall|y: int| 
                #[trigger] satisfies_constraint(y, n as int, k as int) 
                && (y % (k as int)) >= 1 && (y % (k as int)) < (r_i32 as int) 
                ==> min_x_i32 as int <= y
        decreases (k_i32 - r_i32) as int
    {
        if n_i32 % r_i32 == 0 {
            let q = n_i32 / r_i32;
            let x_candidate = q * k_i32 + r_i32;
            if x_candidate < min_x_i32 {
                min_x_i32 = x_candidate;
            }
        }
        r_i32 += 1;
    }

    min_x_i32 as i8
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        valid_input(n as int, k as int)
    ensures 
        result > 0,
        satisfies_constraint(result as int, n as int, k as int),
        forall|x: int| #[trigger] satisfies_constraint(x, n as int, k as int) ==> result as int <= x
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): using fixed helper function */
    compute_minimal_x(n, k)
}
// </vc-code>


}

fn main() {}