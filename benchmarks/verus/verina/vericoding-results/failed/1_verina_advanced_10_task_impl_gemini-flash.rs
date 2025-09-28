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
/* helper modified by LLM (iteration 5): The type nat and int can only be used in ghost code. Modified the inputs and outputs to be u64. */
fn find_exponent_for_prime(n: u64, p: u64) -> (count: u64)
    requires
        p > 0,
    ensures
        p > 0 ==> n % pow(p, count as int) == 0
{
    let mut count: u64 = 0;
    let mut temp_n: u64 = n;
    while temp_n > 0 && temp_n % p == 0
        invariant
            p > 0,
            temp_n * pow(p, count as int) == n
    {
        count = count + 1;
        temp_n = temp_n / p;
    }
    count
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
/* code modified by LLM (iteration 5): Changed the types of the elements pushed to `result` to be u64, as `nat` is a ghost type and cannot be used in executable code. */
{
    let mut result: Vec<(u64, u64)> = Vec::new();

    for i in 0..primes.len() {
        let p = primes[i];
        let p_u64 = p as u64;
        let n_u64 = n as u64;
        let count = find_exponent_for_prime(n_u64, p_u64);
        result.push((p_u64, count));
    }

    proof {
        assert(n as int == spec_fold(result@.map(|(p, e)| (p as nat, e as nat)), 1int));
        assert(forall|i: int| 0 <= i < result.len() ==> (#![trigger] primes@.contains(result[i].0 as nat)));
        assert(forall|p: nat| (#![trigger] primes@.contains(p)) ==> 
            exists|j: int| 0 <= j < result.len() && result[j].0 == p as u64);
    }
    result
}
// </vc-code>

}
fn main() {}