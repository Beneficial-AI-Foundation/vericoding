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
/* helper modified by LLM (iteration 5): No changes were needed for the helpers section, the existing implementation is correct. */
proof fn lemma_impossibility_quadratic_relation(n: int, k: int)
    requires
        valid_input(n, k),
        impossibility_condition(n, k)
    ensures
        forall|x_val: int| x_val >= 0 ==> quadratic_condition(x_val, n, k) == false
{
    let ghost c_term = (2 * (n - 1) - k * (k - 1));
    assert(impossibility_condition(n, k) ==> c_term > 0) by {};
    assert(c_term >= 1) by {}; // Since c_term is an int and c_term > 0

    assert forall|x_val: int| x_val >= 0 implies quadratic_condition(x_val, n, k) == false by {
        assert(c_term >= 1);
        let ghost quadratic_expr = (x_val*x_val - x_val) + c_term;
        if x_val == 0 {
            assert(quadratic_expr == c_term);
            assert(quadratic_expr > 0);
        } else {
            // For x_val >= 1, x_val*x_val - x_val >= 0
            if x_val >= 1 {
                assert(x_val*x_val - x_val >= 0);
                assert(quadratic_expr >= c_term);
                assert(quadratic_expr > 0);
            }
        }
        assert(quadratic_expr > 0);
    }
}
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
/* code modified by LLM (iteration 5): Moved arithmetic expressions and `current_C_ghost` outside of the `while` loop condition to satisfy trait bounds requirements for i8 on the ghost expressions. */
{
    let ghost n_int = n as int;
    let ghost k_int = k as int;
    let ghost current_C_ghost = (2 * (n_int - 1) - k_int * (k_int - 1));

    if current_C_ghost > 0 {
        proof {
            lemma_impossibility_quadratic_relation(n_int, k_int);
        }
        return -1;
    }

    let mut x: i8 = 0;
    while (x as int) < k_int + 1 && (quadratic_condition(x as int, n_int, k_int))
        invariant
            0 <= x as int,
            x as int <= k_int + 1,
            forall|prev_x_val: int| // All previous values satisfied the condition
                0 <= prev_x_val < x as int
                ==>
                quadratic_condition(prev_x_val, n_int, k_int),
            x as int <= k_int + 1
        decreases k_int + 1 - (x as int)
    {
        x = (x + 1) as i8;
    }

    // At this point, `x` is the first integer for which the quadratic condition is false OR `x` has reached `k_int + 1`.
    // We are looking for the *largest* `x_sol` such that `quadratic_condition(x_sol, n, k)` is true for `x_sol >= 0`,
    // AND `next_quadratic_condition(x_sol, n, k)` is true (i.e., `quadratic_condition(x_sol + 1, n, k)` is false).

    // If the loop ran, `x` is the first value where the quadratic condition does NOT hold.
    // So `x - 1` is the largest value where it DOES hold.
    let solution_x_value = (x - 1) as i8;

    let final_result = k - solution_x_value;
    final_result
}
// </vc-code>


}

fn main() {}