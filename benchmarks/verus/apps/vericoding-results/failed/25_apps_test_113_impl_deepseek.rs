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
/* helper modified by LLM (iteration 5): Fixed gcd and lcm specs with proper decreases and verification */

proof fn power_positive(base: int, exp: int)
    requires exp >= 0
    ensures power(base, exp) > 0
    decreases exp
{
    if exp > 0 {
        power_positive(base, exp - 1);
    }
}

proof fn gcd_properties(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures 
        gcd(a, b) >= 0,
        gcd(a, b) % a == 0,
        gcd(a, b) % b == 0
    decreases if a == 0 { b } else { a }
{
    if a == 0 {
    } else if b == 0 {
    } else {
        gcd_properties(b % a, a);
    }
}

spec fn gcd(a: int, b: int) -> int
    decreases if a == 0 { b } else { a }
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else {
        gcd(b % a, a)
    }
}

proof fn lcm_properties(a: int, b: int)
    requires a > 0 && b > 0
    ensures
        lcm(a, b) > 0,
        lcm(a, b) % a == 0,
        lcm(a, b) % b == 0,
        forall|m: int| #[trigger] (m % a) == 0 && #[trigger] (m % b) == 0 && m > 0 ==> lcm(a, b) <= m
{
    gcd_properties(a, b);
    
    forall|m: int|
        ensures (m % a == 0 && m % b == 0 && m > 0) ==> lcm(a, b) <= m
    {
        if m % a == 0 && m % b == 0 && m > 0 {
            let g = gcd(a, b);
            assert(g > 0);
            assert(m == (m / g) * g);
            assert(a == (a / g) * g);
            assert(b == (b / g) * g);
            assert(m >= a * b / g);
        }
    }
}

spec fn lcm(a: int, b: int) -> int
    requires a > 0 && b > 0
{
    a * b / gcd(a, b)
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
    /* code modified by LLM (iteration 5): Fixed ghost code compilation by moving all ghost operations inside proof block */
    let n_val = n as i64;
    let k_val = k as i64;
    
    proof {
        let n_int = n as int;
        let k_int = k as int;
        let pow_10_k = power(10, k_int);
        
        power_positive(10, k_int);
        lcm_properties(n_int, pow_10_k);
        
        let lcm_val_i64 = lcm(n_int, pow_10_k) as i64;
        assert(lcm_val_i64 <= i8::MAX as i64);
        assert(lcm_val_i64 > 0);
    }
    
    let result_val = (n_val * 10i64.pow(k as u32)) as i8;
    result_val
}
// </vc-code>


}

fn main() {}