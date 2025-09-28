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
/* helper modified by LLM (iteration 3): normalize modulo to non-negative remainder */
spec fn mod_positive(x: int, m: int) -> int
    requires
        m > 0,
    ensures
        0 <= result, result < m,
{
    let r = x % m;
    if r < 0 { r + m } else { r }
}

/* helper modified by LLM (iteration 3): relate i8 remainder computation to mod_positive */
proof fn mod_positive_cast(n: i8, m: i8)
    requires
        (m as int) > 0,
    ensures
        if ((n % m) as int) < 0 { (n % m) as int + (m as int) } else { (n % m) as int } == mod_positive(n as int, m as int),
{
    // unfold definition of mod_positive on ints
    assert(mod_positive(n as int, m as int) == {
        let r = (n as int) % (m as int);
        if r < 0 { r + (m as int) } else { r }
    });
    // relate i8 % i8 to int % int via casts
    assert((n % m) as int == (n as int) % (m as int));
    // conclude the required equality
    assert(if ((n % m) as int) < 0 { (n % m) as int + (m as int) } else { (n % m) as int } == mod_positive(n as int, m as int));
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
/* code modified by LLM (iteration 3): compute minimal cost using spec mod_positive and return as i8 */
{
    let n_i = n as int;
    let m_i = m as int;
    let a_i = a as int;
    let b_i = b as int;
    let k_i = mod_positive(n_i, m_i);
    let cost_add = k_i * b_i;
    let cost_remove = (m_i - k_i) * a_i;
    let chosen_i = if cost_add < cost_remove { cost_add } else { cost_remove };

    proof {
        assert(chosen_i == min_cost_to_divisible(n_i, m_i, a_i, b_i));
    }

    let out = chosen_i as i8;
    out
}

// </vc-code>


}

fn main() {}