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
/* helper modified by LLM (iteration 5): added helper for modulo properties and simplified existing helpers */
proof fn lemma_fold_properties(pairs: Seq<(nat, nat)>, acc: int)
    ensures spec_fold(pairs, acc) == acc * spec_fold(pairs, 1)
    decreases pairs.len()
{
    if pairs.len() == 0 {
    } else {
        let (p, e) = pairs[0];
        lemma_fold_properties(pairs.subrange(1, pairs.len() as int), acc * pow(p as int, e as nat));
    }
}

proof fn lemma_fold_append(pairs1: Seq<(nat, nat)>, pairs2: Seq<(nat, nat)>, acc: int)
    ensures spec_fold(pairs1 + pairs2, acc) == spec_fold(pairs2, spec_fold(pairs1, acc))
    decreases pairs1.len()
{
    if pairs1.len() == 0 {
    } else {
        let (p, e) = pairs1[0];
        lemma_fold_append(pairs1.subrange(1, pairs1.len() as int), pairs2, acc * pow(p as int, e as nat));
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
{
    /* code modified by LLM (iteration 5): fixed nat literal syntax and type mismatches */
    let mut result = Vec::new();
    let mut remaining = n;
    
    for i in 0..primes.len()
        invariant
            remaining >= 1,
            n as int == remaining as int * spec_fold(result@, 1),
            forall|j: int| 0 <= j < result.len() ==> primes@.contains(result[j].0),
    {
        let prime = primes[i];
        let mut exponent: nat = 0nat;
        
        while remaining % prime == 0 && remaining > 1
            invariant
                remaining >= 1,
                n as int == remaining as int * pow(prime as int, exponent as nat) * spec_fold(result@, 1),
                forall|j: int| 0 <= j < result.len() ==> primes@.contains(result[j].0),
        {
            remaining = remaining / prime;
            exponent = exponent + 1nat;
        }
        
        if exponent > 0nat {
            result.push((prime, exponent));
        }
    }
    
    if remaining > 1 {
        result.push((remaining, 1nat));
    }
    
    result
}
// </vc-code>

}
fn main() {}