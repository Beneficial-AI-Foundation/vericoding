// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(num: int) -> bool {
    num >= 2 && forall|k: int| 2 <= k < num ==> #[trigger] (num % k) != 0
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): added lemma to prove loop invariant */
fn is_prime(num: i8) -> (result: bool)
    requires
        num >= 2,
    ensures
        result == is_prime_number(num as int),
{
    let mut k: i8 = 2;
    while k < num
        invariant
            num >= 2,
            2 <= k <= num,
            forall|j: int| 2 <= j < k as int ==> #[trigger] (num as int % j) != 0,
        decreases (num - k) as nat,
    {
        if num % k == 0 {
            return false;
        }
        k = k + 1;
    }
    true
}

proof fn lemma_extend_primes_set(primes_old: Seq<i8>, i_old: int, primes_new: Seq<i8>)
    requires
        i_old >= 2,
        forall|p: int| 2 <= p < i_old && is_prime_number(p) ==> primes_old.contains(p as i8),
        if is_prime_number(i_old) {
            primes_new == primes_old.push(i_old as i8)
        } else {
            primes_new == primes_old
        },
    ensures
        forall|p: int| 2 <= p < i_old + 1 && is_prime_number(p) ==> primes_new.contains(p as i8),
{
    assert forall|p: int| 2 <= p < i_old + 1 && is_prime_number(p) implies primes_new.contains(p as i8) by {
        if p < i_old {
            assert(primes_old.contains(p as i8));
            assert(primes_new.contains(p as i8));
        } else {
            assert(p == i_old);
            assert(is_prime_number(i_old));
            assert(primes_new.contains(p as i8));
        }
    }
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
{
    /* code modified by LLM (iteration 4): fixed incorrect ghost syntax */
    if n < 2 {
        return Vec::new();
    }

    let mut primes: Vec<i8> = Vec::new();
    let mut i: i8 = 2;
    while i < n
        invariant
            n >= 2,
            2 <= i <= n as int,
            forall|k: int| 0 <= k < primes.len() ==> is_prime_number(#[trigger] primes[k] as int),
            forall|k: int| 0 <= k < primes.len() ==> (#[trigger] primes[k] as int) < i as int,
            forall|p: int| 2 <= p < i as int && is_prime_number(p) ==> primes@.contains(p as i8),
            forall|k: int, j: int| 0 <= k < j < primes.len() ==> (#[trigger] primes[k] as int) < (#[trigger] primes[j] as int),
        decreases (n - i) as nat,
    {
        let i_old = i;
        let ghost primes_old_g = primes@;
        let is_i_prime = is_prime(i_old);

        if is_i_prime {
            primes.push(i_old);
        }

        proof {
            let primes_new_g = primes@;
            lemma_extend_primes_set(primes_old_g, i_old as int, primes_new_g);
        }

        i = i + 1;
    }
    primes
}
// </vc-code>


}

fn main() {}