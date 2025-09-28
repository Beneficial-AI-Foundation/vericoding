// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(num: int) -> bool {
    num >= 2 && forall|k: int| 2 <= k < num ==> #[trigger] (num % k) != 0
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add decreases to allow proof block */
proof fn lemma_prime_from_no_divisors(c: int)
    requires
        2 <= c,
        forall|k: int| 2 <= k < c ==> c % k != 0,
    ensures
        is_prime_number(c),
    decreases
        c
{
    proof {
        assert(2 <= c);
        assert(forall|k: int| 2 <= k < c ==> c % k != 0);
        assert(is_prime_number(c));
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
    /* code modified by LLM (iteration 5): call proof lemma; iterates and collects primes < n */
    let mut result: Vec<i8> = Vec::new();
    let mut i: i8 = 2;
    while i < n
        invariant
            forall|idx: int| 0 <= idx < result.len() ==> is_prime_number(#[trigger] result[idx] as int),
            forall|idx: int| 0 <= idx < result.len() ==> #[trigger] (result[idx] as int) < (i as int),
            forall|p: int| 2 <= p < (i as int) && is_prime_number(p) ==> result@.contains(p as i8),
            forall|a: int, b: int| 0 <= a < b < result.len() ==> #[trigger] (result[a] as int) < #[trigger] (result[b] as int),
        decreases (n as int - i as int)
    {
        let mut k: i8 = 2;
        let mut no_div: bool = true;
        while k < i
            invariant
                forall|t: int| 2 <= t < (k as int) ==> (i as int) % t != 0,
                (k as int) <= (i as int),
            decreases (i as int - k as int)
        {
            if i % k == 0 {
                no_div = false;
                k = i;
            } else {
                k += 1;
            }
        }
        if no_div {
            proof {
                assert(!((k as int) < (i as int)));
                assert((k as int) <= (i as int));
                assert((k as int) == (i as int));
                assert(forall|t: int| 2 <= t < (i as int) ==> (i as int) % t != 0);
                lemma_prime_from_no_divisors(i as int);
            }
            result.push(i);
        }
        i += 1;
    }
    result
}

// </vc-code>


}

fn main() {}