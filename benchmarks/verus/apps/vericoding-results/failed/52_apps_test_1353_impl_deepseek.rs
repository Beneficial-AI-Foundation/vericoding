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

proof fn lemma_div_mod_relation(n: int, m: int)
    requires
        m > 0,
    ensures
        n == (n / m) * m + (n % m),
        (n % m) >= 0,
        (n % m) < m,
{
    // Standard division with remainder properties
    assert(n == (n / m) * m + (n % m));
    assert((n % m) >= 0);
    assert((n % m) < m);
}

proof fn lemma_ceiling_div_properties(n: int, m: int)
    requires
        n >= 0,
        m > 0,
    ensures
        ((n + m - 1) / m) * m >= n,
        ((n + m - 1) / m) * m - m < n,
{
    let ceiling = (n + m - 1) / m;
    let remainder = n % m;
    
    proof {
        if remainder > 0 {
            assert(ceiling == (n / m) + 1);
            assert(ceiling * m == ((n / m) + 1) * m);
            assert(ceiling * m == (n / m) * m + m);
            assert(n == (n / m) * m + remainder);
            assert(ceiling * m > n);
            assert(ceiling * m - m == (n / m) * m <= n);
        } else {
            assert(remainder == 0);
            assert(ceiling == n / m);
            assert(ceiling * m == n);
            assert(ceiling * m == n);
            assert(ceiling * m - m == n - m < n);
        }
    }
}

proof fn lemma_cost_comparison(n: int, m: int, a: int, b: int)
    requires
        valid_input(n, m, a, b),
    ensures
        optimal_cost(n, m, a, b) == if n * a <= ((n + m - 1) / m) * b {
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
        },
{
    // Follows from the definition
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
    /* code modified by LLM (iteration 5): Fix cast to int in lemma calls */
    let n_int: int = n as int;
    let m_int: int = m as int;
    let a_int: int = a as int;
    let b_int: int = b as int;
    
    proof {
        lemma_div_mod_relation(n_int, m_int);
        lemma_ceiling_div_properties(n_int, m_int);
        lemma_cost_comparison(n_int, m_int, a_int, b_int);
    }
    
    let total_a = n_int * a_int;
    let full_rides = (n_int + m_int - 1) / m_int;
    let total_b_full = full_rides * b_int;
    
    let rides_with_full = n_int / m_int;
    let remaining_rides = n_int % m_int;
    let partial_b = rides_with_full * b_int;
    let remaining_a = remaining_rides * a_int;
    let total_b_remaining = partial_b + remaining_a;
    
    let result_int: int = 
        if total_a <= total_b_full {
            if total_a <= total_b_remaining { total_a } else { total_b_remaining }
        } else {
            if total_b_full <= total_b_remaining { total_b_full } else { total_b_remaining }
        };
    
    assert(0 <= result_int);
    result_int as i8
}
// </vc-code>


}

fn main() {}