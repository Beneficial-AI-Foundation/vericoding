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
/* helper modified by LLM (iteration 5): prove quadratic_condition(0) from C<=0 */
proof fn lemma_C_le_zero_implies_q0(n: int, k: int)
    requires
        2 * (n - 1) - k * (k - 1) <= 0,
    ensures
        quadratic_condition(0, n, k),
{
    assert(0 * 0 - 0 + (2 * (n - 1) - k * (k - 1)) <= 0);
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
{
    /* code modified by LLM (iteration 5): compute using i32 arithmetic and prove correspondence in proof blocks */
    let n32: i32 = n as i32;
    let k32: i32 = k as i32;
    let C32: i32 = 2 * (n32 - 1) - k32 * (k32 - 1);

    if C32 > 0 {
        proof {
            let C: int = 2 * (n as int - 1) - (k as int) * (k as int - 1);
            assert(C > 0);
        }
        return -1;
    } else {
        proof {
            lemma_C_le_zero_implies_q0(n as int, k as int);
        }

        let mut i: i32 = 0;
        while i <= k32 && (i * i - i + C32) <= 0
            invariant
                0 <= i,
                forall|t: i32| 0 <= t && t < i ==> #[trigger] ((t * t - t + C32) <= 0),
            decreases k32 + 1 - i
        {
            i = i + 1;
        }

        let x_i32: i32 = i - 1;
        proof {
            let C: int = 2 * (n as int - 1) - (k as int) * (k as int - 1);
            let x: int = x_i32 as int;

            // From the loop invariant we know the quadratic condition held for all t < i, in particular for x = i-1
            assert((x_i32 * x_i32 - x_i32 + C32) <= 0);
            // relate the i32 arithmetic to the spec-level int arithmetic
            assert(((x_i32 * x_i32 - x_i32 + C32) as int) == x * x - x + C);
            assert(x * x - x + C <= 0);

            assert(x >= 0);
            assert(x <= k as int);

            if x != 0 {
                if i <= k32 {
                    // The loop stopped because the quadratic condition failed at i
                    let inext: int = i as int;
                    assert((inext * inext - inext + C) > 0);
                    assert((x + 1) == inext);
                    assert((x + 1) * (x + 1) - (x + 1) + C > 0);
                } else {
                    // i == k32 + 1, so x == k; prove next_quadratic_condition holds
                    let kp: int = k as int;
                    let val: int = (kp + 1) * (kp + 1) - (kp + 1) + C;
                    // simplify val: val = 2*kp + 2*(n-1)
                    assert(val == 2 * kp + 2 * (n as int - 1));
                    assert(2 * kp + 2 * (n as int - 1) > 0);
                    assert(val > 0);
                    assert((x + 1) * (x + 1) - (x + 1) + C > 0);
                }
            } else {
                // x == 0: lemma establishes quadratic_condition(0)
                lemma_C_le_zero_implies_q0(n as int, k as int);
            }
        }

        let res_i32: i32 = k32 - x_i32;
        return res_i32 as i8;
    }
}

// </vc-code>


}

fn main() {}