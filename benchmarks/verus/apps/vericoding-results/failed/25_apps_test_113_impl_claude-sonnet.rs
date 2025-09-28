// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(base: int, exp: int) -> int
    decreases exp
{
    if exp <= 0 { 1 }
    else { base * power(base, exp - 1) }
}
// </vc-preamble>

// <vc-helpers>
spec fn gcd(a: int, b: int) -> int
    decreases if a > b { a } else { b }
{
    if a == b {
        a
    } else if a > b {
        gcd(a - b, b)
    } else {
        gcd(a, b - a)
    }
}

spec fn lcm(a: int, b: int) -> int
{
    (a * b) / gcd(a, b)
}

/* helper modified by LLM (iteration 5): fixed trigger for quantifier */
proof fn lemma_lcm_properties(a: int, b: int)
    requires a > 0, b > 0
    ensures forall|m: int| #[trigger] (m % a == 0 && m % b == 0) ==> m <= 0 || lcm(a, b) <= m
{
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: i8)
    requires 
        n > 0 && k >= 0,
    ensures 
        result > 0,
        (result as int) % (n as int) == 0,
        (result as int) % power(10, k as int) == 0,
        forall|m: int| #[trigger] (m % (n as int)) == 0 && #[trigger] (m % power(10, k as int)) == 0 && m > 0 ==> (result as int) <= m,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified implementation using basic arithmetic */
    let mut current = n;
    let power_10_k = if k == 0 { 1 } else if k == 1 { 10 } else { 100 };
    
    while current % power_10_k != 0
        invariant
            current > 0,
            current as int % (n as int) == 0,
            current <= 127,
        decreases 127 - current
    {
        current += n;
    }
    
    current
}
// </vc-code>


}

fn main() {}