// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(num: int) -> bool {
    num >= 2 && forall|k: int| 2 <= k < num ==> #[trigger] (num % k) != 0
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added #[trigger] annotation to quantifier in invariant and casted expressions for proper type compatibility */
fn is_prime(num: i8) -> (b: bool)
    requires
        num as int >= 2,
    ensures
        b == is_prime_number(num as int),
{
    let mut i = 2;
    let mut prime = true;
    //#[verifier(spinoff_prover)]
    while i * i <= num as int
        invariant
            2 <= i && i <= (num as int) / 2 + 1,
            prime == (forall|k: int| 2 <= k < i as int ==> #[trigger] (num as int % k) != 0),
        decreases (num as int - i as int)
    {
        if (num as int) % i == 0 {
            prime = false;
        }
        i += 1;
    }
    prime
}
// </vc-helpers>

// <vc-spec>
fn count_up_to(n: i8) -> (result: Vec<i8>)
    requires n as int >= 0
    ensures 
        forall|i: int| 0 <= i < result.len() ==> is_prime_number(#[trigger] result[i] as int),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] (result[i] as int) < (n as int),
        forall|p: int| 2 <= p < (n as int) && is_prime_number(p) ==> result@.contains(p as i8),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] (result[i] as int) < #[trigger] (result[j] as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): implementation preserved from previous iteration with existing invariants */
{
    let mut primes = Vec::new();
    if n >= 2 {
        let mut p: i8 = 2;
        while p < n
            invariant
                2 <= p as int && p as int <= n as int,
                forall|i: int| 0 <= i < primes@.len() ==> #[trigger] is_prime_number(primes@[i] as int),
                forall|i: int| 0 <= i < primes@.len() ==> #[trigger] (primes@[i] as int) < (p as int),
                forall|i: int| 0 <= i < primes@.len() ==> (primes@[i] as int) < (n as int),
                forall|pp: int| 2 <= pp < p as int && is_prime_number(pp) ==> primes@.contains(pp as i8),
                forall|i: int, j: int| 0 <= i < j < primes@.len() ==> #[trigger] (primes@[i] as int) < #[trigger] (primes@[j] as int),
            decreases (n as int - p as int)
        {
            if is_prime(p) {
                primes.push(p);
            }
            p += 1;
        }
    }
    primes
}
// </vc-code>


}

fn main() {}