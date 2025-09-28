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
{
    /* code modified by LLM (iteration 5): Fixed type mismatch by declaring remaining as int and adjusting the invariant for spec_fold call */
    let tracked mut result: Vec<(nat, nat)> = Vec::new();
    let tracked mut remaining: int = n as int;
    let tracked mut i: int = 0;
    while i < primes.len()
        invariant
            0 <= i <= primes.len(),
            n as int == spec_fold(result@, remaining),
        decreases primes.len() - i
    {
        let tracked p: nat = primes[i];
        let tracked mut e: nat = 0;
        let tracked old_remaining = remaining;
        while remaining % (p as int) == 0 && remaining > 0
            invariant
                0 <= e,
                old_remaining == remaining * pow(p as int, e as nat),
            decreases remaining
        {
            e = e + 1nat;
            remaining = remaining / (p as int);
        }
        result.push((p, e));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}