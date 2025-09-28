// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: int, b: int) -> bool {
    n >= 1 && n <= 1000 &&
    m >= 1 && m <= 1000 &&
    a >= 1 && a <= 1000 &&
    b >= 1 && b <= 1000
}

spec fn optimal_cost(n: int, m: int, a: int, b: int) -> int
    recommends valid_input(n, m, a, b)
{
    if n * a <= ((n + m - 1) / m) * b {
        if n * a <= (n / m) * b + (n % m) * a {
            n * a
        } else {
            (n / m) * b + (n % m) * a
        }
    } else {
        if ((n + m - 1) / m) * b <= (n / m) * b + (n % m) * a {
            ((n + m - 1) / m) * b
        } else {
            (n / m) * b + (n % m) * a
        }
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma proofs with proper bounds checking */
proof fn lemma_optimal_cost_bounds(n: int, m: int, a: int, b: int)
    requires
        valid_input(n, m, a, b),
    ensures
        optimal_cost(n, m, a, b) >= 0,
        optimal_cost(n, m, a, b) <= 1000000,
{
    assert(n >= 1 && a >= 1);
    assert(n <= 1000 && a <= 1000);
    assert(b >= 1 && b <= 1000);
    assert(m >= 1 && m <= 1000);
    
    assert(n * a >= 1);
    assert(n * a <= 1000000);
    
    assert((n + m - 1) / m >= 1) by {
        assert(n + m - 1 >= n);
        assert(n >= 1);
        assert(n + m - 1 >= 1);
        assert((n + m - 1) / m >= 1);
    }
    
    assert((n + m - 1) / m <= 1000) by {
        assert(n + m - 1 <= 1000 + 1000 - 1);
        assert(n + m - 1 <= 1999);
        assert((n + m - 1) / m <= 1999);
    }
    
    assert(((n + m - 1) / m) * b <= 1000 * 1000);
    assert((n / m) * b + (n % m) * a <= 1000 * 1000 + 1000 * 1000);
}

proof fn lemma_division_bounds(n: int, m: int)
    requires
        n >= 1 && n <= 1000,
        m >= 1 && m <= 1000,
    ensures
        (n + m - 1) / m >= 1,
        (n + m - 1) / m <= 1000,
        n / m >= 0,
        n / m <= 1000,
        n % m >= 0,
        n % m < m,
{
    assert(n + m - 1 >= n) by {
        assert(m >= 1);
    }
    assert(n >= 1);
    assert(n + m - 1 >= 1);
    assert((n + m - 1) / m >= 1) by {
        assert(n + m - 1 >= m);
    }
    
    assert(n + m - 1 <= 1999);
    assert((n + m - 1) / m <= (n + m - 1));
    assert((n + m - 1) / m <= 1999);
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int, a as int, b as int),
    ensures 
        result >= 0,
        result as int == optimal_cost(n as int, m as int, a as int, b as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use safer arithmetic with bounds checking */
    let n_i32 = n as i32;
    let m_i32 = m as i32;
    let a_i32 = a as i32;
    let b_i32 = b as i32;
    
    proof {
        assert(n_i32 >= 1 && n_i32 <= 1000);
        assert(m_i32 >= 1 && m_i32 <= 1000);
        assert(a_i32 >= 1 && a_i32 <= 1000);
        assert(b_i32 >= 1 && b_i32 <= 1000);
        
        assert(n_i32 * a_i32 <= 1000000);
        assert((n_i32 + m_i32 - 1) / m_i32 <= 1999);
        assert(((n_i32 + m_i32 - 1) / m_i32) * b_i32 <= 1999000);
        assert((n_i32 / m_i32) * b_i32 + (n_i32 % m_i32) * a_i32 <= 2000000);
    }
    
    let cost1 = n_i32 * a_i32;
    let cost2 = ((n_i32 + m_i32 - 1) / m_i32) * b_i32;
    let cost3 = (n_i32 / m_i32) * b_i32 + (n_i32 % m_i32) * a_i32;
    
    let min_cost = if cost1 <= cost2 {
        if cost1 <= cost3 {
            cost1
        } else {
            cost3
        }
    } else {
        if cost2 <= cost3 {
            cost2
        } else {
            cost3
        }
    };
    
    proof {
        let n_int = n as int;
        let m_int = m as int;
        let a_int = a as int;
        let b_int = b as int;
        
        lemma_optimal_cost_bounds(n_int, m_int, a_int, b_int);
        lemma_division_bounds(n_int, m_int);
        
        assert(min_cost >= 1);
        assert(min_cost <= 127);
    }
    
    min_cost as i8
}
// </vc-code>


}

fn main() {}