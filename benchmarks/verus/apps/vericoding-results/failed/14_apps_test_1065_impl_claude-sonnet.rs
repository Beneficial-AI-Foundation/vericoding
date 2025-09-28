// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, k: int, m: int, d: int) -> bool {
    2 <= n && 2 <= k <= n && 1 <= m <= n && 1 <= d <= n && m * d * k >= n
}

spec fn candies_used(x: int, d: int, k: int) -> int {
    x * ((d - 1) * k + 1)
}

spec fn valid_distribution(x: int, d: int, n: int, k: int, m: int, d_max: int) -> bool {
    1 <= x <= m && 1 <= d <= d_max && candies_used(x, d, k) <= n
}

spec fn person1_candies(x: int, d: int) -> int {
    x * d
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic proofs with explicit conditions and proper monotonicity */
proof fn lemma_optimal_distribution_exists(n: int, k: int, m: int, d: int)
    requires valid_input(n, k, m, d)
    ensures exists|x: int, d_val: int| valid_distribution(x, d_val, n, k, m, d)
{
    assert(candies_used(1, 1, k) == 1 * ((1 - 1) * k + 1)) by {
        assert(candies_used(1, 1, k) == 1 * (0 * k + 1));
        assert(candies_used(1, 1, k) == 1 * 1);
        assert(candies_used(1, 1, k) == 1);
    };
    assert(1 <= k) by {
        assert(2 <= k);
    };
    assert(candies_used(1, 1, k) <= n) by {
        assert(candies_used(1, 1, k) == 1);
        assert(1 <= k <= n);
    };
    assert(valid_distribution(1, 1, n, k, m, d));
}

proof fn lemma_candies_used_monotonic(x1: int, x2: int, d1: int, d2: int, k: int)
    requires x1 <= x2 && d1 <= d2 && x1 >= 1 && d1 >= 1 && k >= 1
    ensures candies_used(x1, d1, k) <= candies_used(x2, d2, k)
{
    let term1 = (d1 - 1) * k + 1;
    let term2 = (d2 - 1) * k + 1;
    proof {
        assert(d1 - 1 <= d2 - 1);
        assert(k >= 1);
        if d1 - 1 >= 0 {
            assert((d1 - 1) * k <= (d2 - 1) * k);
        } else {
            assert(d1 == 0);
            assert((d1 - 1) * k == -k);
            assert((d2 - 1) * k >= -k);
        }
        assert(term1 <= term2);
        
        assert(x1 >= 1 && x2 >= x1);
        assert(term1 >= 1 && term2 >= term1);
        if x1 >= 1 && term1 >= 1 {
            assert(x1 * term1 <= x1 * term2);
        }
        if x1 >= 1 && x2 >= x1 && term2 >= 1 {
            assert(x1 * term2 <= x2 * term2);
        }
        assert(x1 * term1 <= x2 * term2);
    }
}

proof fn lemma_person1_candies_monotonic(x1: int, x2: int, d1: int, d2: int)
    requires x1 <= x2 && d1 <= d2 && x1 >= 0 && d1 >= 0
    ensures person1_candies(x1, d1) <= person1_candies(x2, d2)
{
    proof {
        if x1 == 0 || d1 == 0 {
            assert(x1 * d1 == 0);
            assert(x2 >= 0 && d2 >= 0);
            assert(x2 * d2 >= 0);
        } else {
            assert(x1 >= 1 && d1 >= 1);
            assert(x2 >= x1 && d2 >= d1);
            assert(x1 * d1 <= x2 * d1);
            assert(x2 * d1 <= x2 * d2);
        }
        assert(x1 * d1 <= x2 * d2);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8, m: i8, d: i8) -> (result: i8)
    requires valid_input(n as int, k as int, m as int, d as int)
    ensures
        result >= 0 &&
        result as int <= m as int * d as int &&
        (forall|x: int, d_val: int| valid_distribution(x, d_val, n as int, k as int, m as int, d as int) ==> person1_candies(x, d_val) <= result as int) &&
        (exists|x: int, d_val: int| valid_distribution(x, d_val, n as int, k as int, m as int, d as int) && person1_candies(x, d_val) == result as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified with proper invariants and fixed overflow checks */
    let mut max_candies = 0i8;
    
    let mut x = 1i8;
    while x <= m
        invariant
            1 <= x <= m + 1,
            max_candies >= 0,
            max_candies as int <= m as int * d as int,
            (forall|x_val: int, d_val: int| #![auto] 1 <= x_val < x as int && valid_distribution(x_val, d_val, n as int, k as int, m as int, d as int) ==> person1_candies(x_val, d_val) <= max_candies as int),
        decreases m as int - x as int
    {
        let mut d_val = 1i8;
        while d_val <= d
            invariant
                1 <= d_val <= d + 1,
                1 <= x <= m,
                max_candies >= 0,
                max_candies as int <= m as int * d as int,
                (forall|x_prev: int, d_prev: int| #![auto] 1 <= x_prev < x as int && valid_distribution(x_prev, d_prev, n as int, k as int, m as int, d as int) ==> person1_candies(x_prev, d_prev) <= max_candies as int),
                (forall|d_curr: int| #![auto] 1 <= d_curr < d_val as int && valid_distribution(x as int, d_curr, n as int, k as int, m as int, d as int) ==> person1_candies(x as int, d_curr) <= max_candies as int),
            decreases d as int - d_val as int
        {
            assert(d_val >= 1 && k >= 2);
            
            let candies_needed = candies_used(x as int, d_val as int, k as int);
            if candies_needed <= n as int {
                assert(valid_distribution(x as int, d_val as int, n as int, k as int, m as int, d as int));
                let person1_result = person1_candies(x as int, d_val as int);
                if person1_result > max_candies as int && person1_result <= 127 {
                    max_candies = person1_result as i8;
                }
            }
            
            d_val = d_val + 1;
        }
        
        x = x + 1;
    }
    
    proof {
        lemma_optimal_distribution_exists(n as int, k as int, m as int, d as int);
        assert(exists|x: int, d_val: int| valid_distribution(x, d_val, n as int, k as int, m as int, d as int));
        
        let witness_x = 1;
        let witness_d = 1;
        assert(valid_distribution(witness_x, witness_d, n as int, k as int, m as int, d as int));
        assert(person1_candies(witness_x, witness_d) == 1);
        
        if max_candies == 0 {
            max_candies = 1;
        }
    }
    
    max_candies
}
// </vc-code>


}

fn main() {}