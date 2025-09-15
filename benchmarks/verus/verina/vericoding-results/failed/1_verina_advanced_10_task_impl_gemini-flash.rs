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
/* helper modified by LLM (iteration 5): Corrected `while` loop invariant type for `current_n_local` and `count` to `nat` and ensured `current_n_local` calculation in invariant is within `nat` bounds. */
spec fn find_exponent_for_prime(n: nat, p: nat) -> nat {
    if p == 0 {
        0
    } else {
        let mut count: nat = 0;
        let mut current_n_local: nat = n;

        while current_n_local % p == 0 && current_n_local > 0
            invariant
                n as int == (current_n_local as int * pow(p as int, count as nat)),
                count is nat,
                current_n_local is nat,
            decreases current_n_local
        {
            count = count + 1;
            current_n_local = current_n_local / p;
        }
        count
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
    /* code modified by LLM (iteration 5): Fixed type errors in the `while` loop conditions by casting `i` to `int` when accessing `primes.len()` or `primes[i as int]`, and ensuring literals like `0` and `1` are used as `nat` in ghost contexts. Also ensured `Exponent` is evaluated based on `n` rather than `current_n` */
    let mut result_vec: Vec<(nat, nat)> = Vec::new();
    let mut current_n_val: nat = n;
    let mut i: nat = 0;

    while (i as int) < primes.len()
        invariant
            0 <= i as int <= primes.len(),
            forall|k: int| 0 <= k < result_vec.len() ==> primes@.contains(result_vec[k].0),
            n as int == spec_fold(result_vec@, 1int) * (current_n_val as int),
            current_n_val >= 1,
            forall|idx: int| 0 <= idx < i as int ==> {
                let p_idx = primes[idx];
                if p_idx > (0 as nat) {
                    let exponent_factor = find_exponent_for_prime(n, p_idx);
                    if exponent_factor > (0 as nat) {
                        result_vec@.contains((p_idx, exponent_factor))
                    } else {
                        !result_vec@.map(|x: (nat, nat)| x.0).contains(p_idx)
                    }
                } else { true }
            },
    {
        let p = primes[i as int];
        if p > (0 as nat) {
            let exponent = find_exponent_for_prime(n, p);
            if exponent > (0 as nat) {
                result_vec.push((p, exponent));
                current_n_val = current_n_val / (pow(p as int, exponent as nat) as nat);
            }
        }
        i = i + (1 as nat);
    }

    result_vec
}
// </vc-code>

}
fn main() {}