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
/* helper modified by LLM (iteration 5): trivial lemma that pow(p, 0) == 1 */
proof fn pow_zero(p: int)
    ensures
        pow(p, 0) == 1,
{
    proof {
        assert(pow(p, 0) == 1);
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
    /* code modified by LLM (iteration 5): compute exponents using tracked ghost vars for rem and e to allow spec arithmetic */
    let mut res: Vec<(nat, nat)> = Vec::new();
    let mut rem: tracked nat = n;
    let mut i: int = 0;

    while i < primes.len()
        invariant
            res.len() == i,
            spec_fold(res@, rem as int) == n as int,
        decreases
            (primes.len() - i)
    {
        let p: nat = primes[i];
        let mut e: tracked nat = 0;

        while rem % p == 0
            invariant
                spec_fold(res@, rem as int * pow(p as int, e)) == n as int,
            decreases
                rem as int
        {
            rem = rem / p;
            e = e + 1;
        }

        res.push((p, e));
        i = i + 1;
    }

    res
}

// </vc-code>

}
fn main() {}