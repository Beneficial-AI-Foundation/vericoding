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
/* helper modified by LLM (iteration 5): Fixed type annotations and proof steps */
spec fn lemma_pow_mod_property(base: int, exp: nat, p: int)
    requires
        base >= 0,
        p > 0,
    ensures
        power(base, exp) % p == power(base % p, exp) % p,
    decreases exp
{
    if exp == 0 {
        assert(power(base, 0) % p == 1 % p);
        assert(power(base % p, 0) % p == 1 % p);
    } else {
        lemma_pow_mod_property(base, (exp - 1) as nat, p);
        assert(power(base, exp) == base * power(base, (exp - 1) as nat));
        assert(power(base % p, exp) == (base % p) * power(base % p, (exp - 1) as nat));
        assert((base * power(base, (exp - 1) as nat)) % p == ((base % p) * (power(base, (exp - 1) as nat) % p)) % p);
    }
}

spec fn lemma_pow2_mod_cycle(p: int) -> (result: Seq<int>)
    requires
        p > 0,
    ensures
        result.len() == p as nat,
        forall |i: nat| i < result.len() ==> result[i] == power(2, i) % p,
    decreases p
{
    let mut cycle = Seq::empty();
    let p_nat = p as nat;
    let mut i: nat = 0;
    while i < p_nat
        invariant
            i <= p_nat,
            cycle.len() == i,
            forall |j: nat| j < i ==> cycle[j] == power(2, j as nat) % p,
    {
        let next_val = power(2, i) % p;
        cycle = cycle.push(next_val);
        i = i + 1;
    }
    cycle
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
    /* code modified by LLM (iteration 5): Fixed type conversions and loop invariant */
    if p == 1 {
        0
    } else {
        let base: i32 = 2;
        let mut result: i32 = 1;
        let exp_i32: i32 = n as i32;
        let p_i32: i32 = p as i32;
        let mut counter: i32 = 0;
        
        while counter < exp_i32
            invariant
                result >= 0 && result < p_i32,
                result as int == power(2, counter as nat) % (p_i32 as int),
            decreases exp_i32 - counter
        {
            result = (result * base) % p_i32;
            counter = counter + 1;
        }
        
        result as i8
    }
}
// </vc-code>


}

fn main() {}