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
/* helper modified by LLM (iteration 4): proof that power(base, k+1) = base * power(base, k) */
proof fn power_succ(base: int, k: nat)
    ensures
        power(base, k + 1) == base * power(base, k),
    decreases k
{
    if k == 0 {
        assert(power(base, 1) == base * power(base, 0));
    } else {
        power_succ(base, (k - 1) as nat);
        assert(power(base, k + 1) == base * power(base, (k + 1 - 1) as nat));
        assert((k + 1 - 1) as nat == k);
        assert(power(base, (k + 1 - 1) as nat) == power(base, k));
        assert(power(base, k + 1) == base * power(base, k));
    }
}

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
{
    /* code modified by LLM (iteration 4): compute 2^n mod p using a runtime i8 accumulator and a verified invariant */
    let mut i: i8 = 0;
    let mut cur: i8 = 1 % p;
    while i < n
        invariant
            i >= 0,
            i <= n,
            (cur as int) == power(2, i as nat) % (p as int),
        decreases (n - i) as nat
    {
        cur = (cur * 2) % p;
        i = i + 1;
    }
    let result: i8 = cur;
    result
}

// </vc-code>


}

fn main() {}