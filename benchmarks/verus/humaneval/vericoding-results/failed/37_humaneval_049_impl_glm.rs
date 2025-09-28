// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(base: int, exp: nat) -> int
    decreases exp
{
    if exp == 0 {
        1
    } else {
        base * power(base, (exp - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn modp(n: i8, p: i8) -> (result: i8)
    requires 
        n >= 0 && p > 0,
    ensures 
        result >= 0 && result < p,
        result as int == power(2, n as nat) % (p as int),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): use i16 for intermediate computation to avoid overflow */
{
    let mut result: i8 = 1 % p;
    let mut k: i8 = 0;
    while k < n
        invariant
            0 <= k <= n,
            0 <= result < p,
            result as int == power(2, k as nat) % (p as int),
        decreases (n - k),
    {
        let temp = (result as i16) * 2;
        let mod_val = temp % (p as i16);
        result = mod_val as i8;
        k = k + 1;
    }
    result
}
// </vc-code>


}

fn main() {}