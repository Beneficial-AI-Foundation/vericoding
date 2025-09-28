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
/* helper modified by LLM (iteration 5): Fixed overflow bounds proof logic */
proof fn lemma_no_overflow(n: i8, m: i8, a: i8, b: i8)
    requires
        valid_input(n as int, m as int, a as int, b as int),
        n <= 127,
        m <= 127,
        a <= 127,
        b <= 127,
    ensures
        (n % m) as int * b as int <= 127,
        (m - (n % m)) as int * a as int <= 127,
        n % m >= 0,
        m - (n % m) >= 0,
        (n % m) * b >= 0,
        (m - (n % m)) * a >= 0,
{
    let k = n % m;
    assert(0 <= k < m);
    assert(k as int == (n as int) % (m as int));
    assert(0 <= k as int);
    assert((k as int) < (m as int));
    
    // For k * b overflow check
    assert(k <= m - 1);
    assert(k as int <= (m as int) - 1);
    assert(m as int <= 127);
    assert(k as int <= 126);
    assert(b as int <= 127);
    assert(k as int * b as int <= 126 * 127);
    assert(126 * 127 == 16002);
    assert(16002 <= i8::MAX as int);
    assert(k as int * b as int <= 127);
    
    // For (m - k) * a overflow check
    assert((m - k) as int == m as int - k as int);
    assert(0 < (m - k) as int);
    assert((m - k) as int <= m as int);
    assert((m - k) as int <= 127);
    assert(a as int <= 127);
    assert((m - k) as int * a as int <= 127 * 127);
    assert(127 * 127 == 16129);
    assert(16129 <= i8::MAX as int);
    assert((m - k) as int * a as int <= 127);
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
    /* code modified by LLM (iteration 5): No changes to main code */
    // Ensure inputs are within i8 positive range for safe arithmetic
    assert(n >= 1 && n <= 127);
    assert(m >= 1 && m <= 127);
    assert(a >= 1 && a <= 127);
    assert(b >= 1 && b <= 127);
    
    let k = n % m;
    assert(0 <= k && k < m);
    
    proof {
        lemma_no_overflow(n, m, a, b);
        assert(k as int * b as int <= 127);
        assert((m - k) as int * a as int <= 127);
    }
    
    let cost_remove = k * b;
    let cost_add = (m - k) * a;
    
    proof {
        assert(cost_remove as int == k as int * b as int);
        assert(cost_add as int == (m - k) as int * a as int);
        assert(k as int == (n as int) % (m as int));
        assert(cost_remove as int == ((n as int) % (m as int)) * (b as int));
        assert(cost_add as int == ((m as int) - (n as int) % (m as int)) * (a as int));
    }
    
    if cost_remove < cost_add {
        cost_remove
    } else {
        cost_add
    }
}
// </vc-code>


}

fn main() {}