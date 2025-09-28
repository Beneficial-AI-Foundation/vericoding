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
/* helper modified by LLM (iteration 5): fixed modular arithmetic properties and bounds checking */
proof fn power_two_mod_inductive(exp: nat, p: int)
    requires p > 0, exp > 0
    ensures power(2, exp) % p == ((power(2, (exp - 1) as nat) % p) * 2) % p
    decreases exp
{
    if exp == 1 {
        assert(power(2, 1) == 2 * power(2, 0));
        assert(power(2, 0) == 1);
        assert(power(2, 1) == 2);
        assert(2 % p == (1 * 2) % p);
    } else {
        power_two_mod_inductive((exp - 1) as nat, p);
        assert(power(2, exp) == 2 * power(2, (exp - 1) as nat));
    }
}

proof fn modular_arithmetic_lemma(a: int, p: int)
    requires p > 0
    ensures (a * 2) % p == ((a % p) * 2) % p
{
}

proof fn mod_bounds_lemma(a: int, p: int)
    requires p > 0
    ensures 0 <= a % p < p
{
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
    /* code modified by LLM (iteration 5): fixed ghost/exec separation for modular arithmetic */
    if n == 0 {
        return 1 % p;
    }
    
    let mut result: i8 = 1;
    let mut i: i8 = 0;
    
    proof {
        mod_bounds_lemma(1, p as int);
    }
    
    while i < n
        invariant
            0 <= i <= n,
            0 <= result < p,
            result as int == power(2, i as nat) % (p as int),
        decreases n - i
    {
        proof {
            power_two_mod_inductive((i + 1) as nat, p as int);
            modular_arithmetic_lemma(result as int, p as int);
            mod_bounds_lemma((result as int * 2), p as int);
        }
        
        let ghost old_result = result as int;
        let temp = (result * 2) % p;
        result = temp;
        i = i + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}