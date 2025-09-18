// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed undefined pow3 and simplified arithmetic lemma */
proof fn lemma_arithmetic_identity(n: nat)
    ensures
        n * (2 * n - 1) * (2 * n + 1) == 4 * (n * n * n) - n,
{
    if n == 0 {
    } else {
        lemma_arithmetic_identity((n - 1) as nat);
        assert(n * (2 * n - 1) * (2 * n + 1) == 4 * (n * n * n) - n) by {
            calc! {
                n * (2 * n - 1) * (2 * n + 1);
                == n * (4 * n * n - 1);
                == 4 * n * n * n - n;
                == 4 * (n * n * n) - n;
            }
        };
    }
}

spec fn square(x: int) -> int {
    x * x
}

proof fn lemma_loop_step(i: nat, next_i: nat)
    requires
        i >= 0,
        next_i == i + 1,
    ensures
        (next_i as int * (2 * next_i as int - 1) * (2 * next_i as int + 1)) / 3 == 
        (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3 + square(2 * i as int + 1),
{
    assert((next_i as int * (2 * next_i as int - 1) * (2 * next_i as int + 1)) == 
           (i as int * (2 * i as int - 1) * (2 * i as int + 1)) + 3 * square(2 * i as int + 1));
}
// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed loop invariant and arithmetic calculation */
{
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            sum as int == (i as int * (2 * i as int - 1) * (2 * i as int + 1)) / 3,
        decreases n - i,
    {
        let odd_num = 2 * i + 1;
        let next_i = i + 1;
        proof {
            lemma_loop_step(i as nat, next_i as nat);
        }
        sum = sum + odd_num * odd_num;
        i = next_i;
    }
    
    sum
}
// </vc-code>

}
fn main() {}