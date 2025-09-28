// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove remainder less than divisor */
proof fn mod_less_than_divisor(n: nat, m: nat)
    requires
        m > 0,
    ensures
        n % m < m,
{
    proof {
        assert(n % m < m);
    }
}

// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute last digit using annotated nat for 10 */
    let ten: nat = 10;
    let result = n % ten;
    proof {
        mod_less_than_divisor(n, ten);
    }
    result
}

// </vc-code>

}
fn main() {}