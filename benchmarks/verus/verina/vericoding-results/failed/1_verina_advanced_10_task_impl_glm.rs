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
/* helper modified by LLM (iteration 2): fixed ensures clause syntax by adding curly braces */
spec fn find_exponent(n: nat, p: nat) -> (exponent: nat)
    requires is_prime(p),
    ensures {
        n as int == pow(p as int, exponent) * (n / pow(p, exponent)) as int,
        n / pow(p, exponent + 1) == 0,
    }
{
    if n == 0 {
        0
    } else if n % p == 0 {
        1 + find_exponent(n / p, p)
    } else {
        0
    }
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
/* code modified by LLM (iteration 2): no changes needed, but helper function syntax fixed */
{
    let mut exponents: Vec<(nat, nat)> = Vec::new();
    let mut remaining = n;
    
    for i in 0..primes.len()
        invariant
            remaining <= n,
            n as int == remaining as int * spec_fold(exponents@, 1int),
            forall|k: int| 0 <= k < exponents.len() ==> primes@.contains(exponents[k].0),
            forall|k: int| 0 <= k < i ==> primes@.contains(primes[k])
    {
        let p = primes[i];
        let exp = find_exponent(remaining, p);
        if exp > 0 {
            exponents.push((p, exp));
            remaining = remaining / pow(p, exp);
        }
    }
    
    exponents
}
// </vc-code>

}
fn main() {}