// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {

spec fn is_prime(n: nat) -> bool {
    arbitrary()
}

spec fn spec_fold(pairs: Seq<(nat, nat)>, acc: int) -> int
    decreases pairs.len()
{
    if pairs.len() == 0 {
        acc
    } else {
        let (p, e) = pairs[0];
        spec_fold(pairs.subrange(1, pairs.len() as int), acc * pow(p as int, e as nat))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Simplified proof helpers and fixed nat/int usage */
proof fn lemma_pow_ge_zero(base: int, exp: nat) 
    ensures base >= 0 ==> pow(base, exp) >= 0
{
}

// </vc-helpers>

// <vc-spec>
fn find_exponents(n: nat, primes: Vec<nat>) -> (result: Vec<(nat, nat)>)
    requires
        forall|i: int| 0 <= i < primes.len() ==> is_prime(primes[i]),
    ensures
        n as int == spec_fold(result@, 1int),
        forall|i: int| 0 <= i < result.len() ==> (#[trigger] primes@.contains(result[i].0)),
        forall|p: nat| (#[trigger] primes@.contains(p)) ==> 
            exists|j: int| 0 <= j < result.len() && result[j].0 == p,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Removed nat conversions and fixed type errors */
{
    let mut result: Vec<(nat, nat)> = Vec::new();
    let mut remaining = n;
    let mut index = 0;
    
    while index < primes.len()
        invariant
            remaining >= 1,
            n as int == spec_fold(result@, remaining as int),
            forall|i: int| 0 <= i < result.len() ==> (#[trigger] primes@.contains(result[i].0)),
            forall|p: nat| (#[trigger] primes@.contains(p)) ==> 
                exists|j: int| 0 <= j < result.len() && result[j].0 == p,
        decreases primes.len() - index
    {
        let p = primes[index];
        let mut count = 0;
        let old_remaining = remaining;
        
        while remaining % p == 0
            invariant
                remaining >= 1,
                count >= 0,
                remaining * pow(p as int, count as nat) == old_remaining as int,
            decreases remaining
        {
            remaining = remaining / p;
            count = count + 1;
        }
        
        if count > 0 {
            result.push((p, count));
        }
        
        index = index + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}