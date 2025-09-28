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
/* helper modified by LLM (iteration 5): strengthened lemma preconditions and added arithmetic proofs */
fn lemma_bounds_hold(n: i8, m: i8, a: i8, b: i8)
    requires
        valid_input(n as int, m as int, a as int, b as int),
        n <= 127,
        m <= 127,
        a <= 127,
        b <= 127
    ensures
        (n % m) as int * b as int <= 127,
        (m - (n % m)) as int * a as int <= 127
{
    let k = n % m;
    proof {
        assert(k >= 0);
        assert(k < m);
        assert(k <= m - 1);
        assert(k <= 126);
        assert(k as int * b as int <= 126 * 127);
        assert(k as int * b as int <= 127);
        
        assert(m - k >= 1);
        assert(m - k <= m);
        assert(m - k <= 127);
        assert((m - k) as int * a as int <= 127 * 127);
        assert((m - k) as int * a as int <= 127);
    }
}

fn safe_mul_i8(x: i8, y: i8) -> (result: i8)
    requires
        x >= 0,
        y >= 0,
        x as int * y as int <= 127
    ensures
        result as int == x as int * y as int
{
    x * y
}
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
{
    /* code modified by LLM (iteration 5): use lemma and safe multiplication to prove bounds */
    
    lemma_bounds_hold(n, m, a, b);
    
    let k = n % m;
    
    let cost_remove = safe_mul_i8(k, b);
    let cost_add = safe_mul_i8(m - k, a);
    
    if cost_remove < cost_add {
        cost_remove
    } else {
        cost_add
    }
}
// </vc-code>


}

fn main() {}