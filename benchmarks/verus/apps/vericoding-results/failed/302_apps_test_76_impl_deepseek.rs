// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, m: int, a: int, b: int) -> bool {
    n >= 1 && m >= 1 && a >= 1 && b >= 1
}

spec fn min_cost_to_divisible(n: int, m: int, a: int, b: int) -> int {
    let k = n % m;
    if k * b < (m - k) * a { k * b } else { (m - k) * a }
}
// </vc-preamble>

// <vc-helpers>

proof fn division_property_lemma(n: int, m: int)
    requires
        m > 0,
    ensures
        n % m >= 0,
        n % m < m,
{
    // Basic property of modulo
}

proof fn cost_comparison_lemma(k: int, m: int, a: int, b: int)
    requires
        k >= 0,
        m > 0,
        a >= 0,
        b >= 0,
        k < m,
    ensures
        k * b <= (m - k) * a || (m - k) * a <= k * b,
        min_cost_to_divisible(k + m * 0, m, a, b) == if k * b < (m - k) * a { k * b } else { (m - k) * a },
{
    // The minimum of two values always exists and equals the smaller one
    // The specific formula matches the min_cost_to_divisible definition
}

/* helper modified by LLM (iteration 5): Cleaned up helpers - removed redundant modulo function */

// </vc-helpers>

// <vc-spec>
fn solve(n: i8, m: i8, a: i8, b: i8) -> (result: i8)
    requires 
        valid_input(n as int, m as int, a as int, b as int)
    ensures 
        result as int == min_cost_to_divisible(n as int, m as int, a as int, b as int),
        result as int >= 0
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added variable declarations and used result variable for verification */ {
    let rem = (n % m) as i8;
    let mut result: i8;
    
    proof {
        division_property_lemma(n as int, m as int);
        cost_comparison_lemma((rem as int), m as int, a as int, b as int);
    }
    
    let cost1 = rem * b;
    let cost2 = (m - rem) * a;
    
    if cost1 < cost2 {
        result = cost1;
    } else {
        result = cost2;
    }
    
    result
}
// </vc-code>


}

fn main() {}