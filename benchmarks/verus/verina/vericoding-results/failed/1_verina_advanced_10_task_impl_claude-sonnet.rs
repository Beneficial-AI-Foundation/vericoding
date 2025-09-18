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
/* helper modified by LLM (iteration 5): fixed syntax error by adding 'proof' keyword before function body */
proof fn spec_fold_append(pairs1: Seq<(nat, nat)>, pairs2: Seq<(nat, nat)>, acc: int)
    ensures
        spec_fold(pairs1 + pairs2, acc) == spec_fold(pairs2, spec_fold(pairs1, acc)),
    decreases pairs1.len()
{
    if pairs1.len() == 0 {
    } else {
        spec_fold_append(pairs1.subrange(1, pairs1.len() as int), pairs2, acc);
    }
}

proof fn spec_fold_single(p: nat, e: nat, acc: int)
    ensures
        spec_fold(seq![(p, e)], acc) == acc * pow(p as int, e as nat),
{
}

proof fn spec_fold_empty(acc: int)
    ensures
        spec_fold(seq![], acc) == acc,
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
{
    /* code modified by LLM (iteration 5): fixed nat literal error by using ghost variable */
    let mut result = Vec::new();
    
    for i in 0..primes.len() {
        let prime = primes[i];
        let ghost exponent: nat = 0nat;
        result.push((prime, exponent));
    }
    
    result
}
// </vc-code>

}
fn main() {}