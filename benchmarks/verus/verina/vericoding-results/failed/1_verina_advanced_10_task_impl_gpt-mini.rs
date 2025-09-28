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
/* helper modified by LLM (iteration 5): dummy helper to satisfy verifier */
proof fn helpers_dummy() { }

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
    /* code modified by LLM (iteration 5): use vstd::vec::Vec::new_tracked and compute exponents for each prime */
    let tracked mut res: vstd::vec::Vec<(nat, nat)> = vstd::vec::Vec::new_tracked();
    let ghost mut rem: nat = n;
    let mut j: usize = 0usize;
    while j < primes.len()
        invariant
            j <= primes.len(),
            spec_fold(res@, 1int) * (rem as int) == n as int,
        decreases
            primes.len() - j
    {
        let p: nat = primes[j];
        let ghost mut e: nat = 0;
        proof {
            while rem != (0 as nat) && p > (1 as nat) && rem % p == (0 as nat)
                invariant
                    spec_fold(res@, 1int) * (pow(p as int, e as nat) * (rem as int)) == n as int,
                    0 <= (e as int),
                decreases
                    rem
            {
                rem = rem / p;
                e = e + (1 as nat);
            }
        }
        res.push((p, e));
        j = j + 1usize;
    }
    res
}

// </vc-code>

}
fn main() {}