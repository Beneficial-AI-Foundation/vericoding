// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added spec function for sum formula and fixed algebraic proof */
spec fn sum_formula(n: int) -> int {
    if n <= 0 {
        0
    } else {
        (n * (2 * n - 1) * (2 * n + 1)) / 3
    }
}

proof fn sum_formula_step(i: nat)
    ensures
        sum_formula((i + 1) as int) == sum_formula(i as int) + (2 * i + 1) * (2 * i + 1),
{
    if i == 0 {
        assert(sum_formula(1) == 1 * 1 * 3 / 3);
        assert(sum_formula(1) == 1);
        assert(sum_formula(0) == 0);
        assert((2 * 0 + 1) * (2 * 0 + 1) == 1);
    } else {
        let n = (i + 1) as int;
        let prev = i as int;
        assert(sum_formula(n) == (n * (2 * n - 1) * (2 * n + 1)) / 3);
        assert(sum_formula(prev) == (prev * (2 * prev - 1) * (2 * prev + 1)) / 3);
        
        // Expand the formulas
        let next_val = n * (2 * n - 1) * (2 * n + 1);
        let prev_val = prev * (2 * prev - 1) * (2 * prev + 1);
        
        // n = prev + 1, so 2*n - 1 = 2*prev + 1 and 2*n + 1 = 2*prev + 3
        assert(next_val == (prev + 1) * (2 * prev + 1) * (2 * prev + 3));
        
        // Expand (prev + 1) * (2 * prev + 1) * (2 * prev + 3)
        assert(next_val == prev * (2 * prev + 1) * (2 * prev + 3) + (2 * prev + 1) * (2 * prev + 3));
        
        // Expand prev * (2 * prev + 1) * (2 * prev + 3)
        assert(prev * (2 * prev + 1) * (2 * prev + 3) == prev * (2 * prev + 1) * (2 * prev + 1) + prev * (2 * prev + 1) * 2);
        assert(prev * (2 * prev + 1) * (2 * prev + 1) == prev * (4 * prev * prev + 4 * prev + 1));
        assert(prev * (2 * prev + 1) * 2 == 2 * prev * (2 * prev + 1));
        
        // prev * (2 * prev - 1) * (2 * prev + 1) = prev * (4 * prev^2 - 1)
        assert(prev_val == prev * (4 * prev * prev - 1));
        
        // The difference simplifies to (2 * prev + 1)^2
        assert(next_val - prev_val == 3 * (2 * prev + 1) * (2 * prev + 1));
        assert((next_val - prev_val) / 3 == (2 * prev + 1) * (2 * prev + 1));
        assert(sum_formula(n) - sum_formula(prev) == (2 * prev + 1) * (2 * prev + 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn sum_of_squares_of_first_n_odd_numbers(n: u32) -> (result: u32)
    requires n >= 0,
    ensures
        result as int == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Simplified implementation without overflow checks */
    if n == 0 {
        return 0;
    }
    
    let mut sum: u32 = 0;
    let mut i: u32 = 0;
    
    assert(sum_formula(0) == 0);
    assert(sum as int == sum_formula(i as int));
    
    while i < n
        invariant
            i <= n,
            sum as int == sum_formula(i as int),
        decreases n - i,
    {
        let odd = 2 * i + 1;
        let square = odd * odd;
        
        proof {
            sum_formula_step(i as nat);
            assert(sum_formula((i + 1) as int) == sum_formula(i as int) + (2 * i as int + 1) * (2 * i as int + 1));
            assert(odd as int == 2 * i as int + 1);
            assert(square as int == odd as int * odd as int);
            assert(square as int == (2 * i as int + 1) * (2 * i as int + 1));
        }
        
        sum = sum + square;
        i = i + 1;
        
        assert(sum as int == sum_formula(i as int));
    }
    
    assert(i == n);
    assert(sum as int == sum_formula(n as int));
    assert(sum_formula(n as int) == (n as int * (2 * n as int - 1) * (2 * n as int + 1)) / 3);
    
    sum
}
// </vc-code>

}
fn main() {}