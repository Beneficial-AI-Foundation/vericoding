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
/* helper modified by LLM (iteration 5): fix function signature syntax for multiple return values */
proof fn lemma_pow_properties() ensures forall |b: int, e: nat| b > 0 ==> pow(b, e) > 0 { }

proof fn lemma_fold_nonzero(pairs: Seq<(nat, nat)>, acc: int) 
    requires
        acc != 0,
        forall |i: int| 0 <= i < pairs.len() ==> pairs[i].0 > 0,
    ensures
        spec_fold(pairs, acc) != 0
    decreases pairs.len()
{
    if pairs.len() == 0 {
    } else {
        let (p, e) = pairs[0];
        lemma_pow_properties();
        assert(pow(p as int, e as nat) > 0);
        lemma_fold_nonzero(pairs.subrange(1, pairs.len() as int), acc * pow(p as int, e as nat));
    }
}

fn find_power_factor(mut n: nat, p: nat) -> (nat, nat)
    requires
        n > 0,
        p > 1,
    ensures
        n == result.1 * pow(p as int, result.0 as nat),
        result.1 % p != 0
{
    let mut count = 0;
    let mut current = n;
    
    while current % p == 0
        invariant
            current > 0,
            count >= 0,
            n == current * pow(p as int, count as nat)
        decreases current
    {
        count = count + 1;
        current = current / p;
    }
    
    (count, current)
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
/* code modified by LLM (iteration 5): handle find_power_factor return values properly */
{
    let mut result = Vec::new();
    let mut remaining = n;
    
    proof {
        lemma_fold_nonzero(Seq::empty(), 1);
    }
    
    let mut i = 0;
    while i < primes.len()
        invariant
            0 <= i <= primes.len(),
            remaining > 0,
            forall|j: int| 0 <= j < result.len() ==> primes@.contains(result[j].0),
            n as int == spec_fold(result@, 1) * remaining,
            forall|k: int| 0 <= k < primes.len() && k < i ==> 
                exists|j: int| 0 <= j < result.len() && result[j].0 == primes[k],
        decreases primes.len() - i
    {
        let p = primes[i];
        
        if remaining % p == 0 {
            let (e, new_remaining) = find_power_factor(remaining, p);
            result.push((p, e));
            remaining = new_remaining;
            
            proof {
                assert(spec_fold(result@, 1) == spec_fold(result@.drop_last(1), 1) * pow(p as int, e as nat));
            }
        }
        
        i = i + 1;
    }
    
    assert(remaining == 1) by {
        lemma_fold_nonzero(result@, 1);
    };
    
    result
}
// </vc-code>

}
fn main() {}