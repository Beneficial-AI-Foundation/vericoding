// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(num: int) -> bool {
    num >= 2 && forall|k: int| 2 <= k < num ==> #[trigger] (num % k) != 0
}

// </vc-preamble>

// <vc-helpers>
fn is_prime_exec(num: int) -> (result: bool)
    recommends num >= 0
    ensures result <==> is_prime_number(num)
{
    /* helper modified by LLM (iteration 5): fixed compilation error in invariant */
    if num < 2 {
        false
    } else {
        let mut i = 2;
        while i < num
            invariant
                2 <= i <= num,
                forall|k: int| 2 <= k < i ==> num % k != 0,
            decreases num - i
        {
            if num % i == 0 {
                return false;
            }
            i = i + 1;
        }
        true
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
    /* code modified by LLM (iteration 5): fixed comma in invariant condition */
    let mut primes = Vec::new();
    let mut i = 2;
    while i < (n as int)
        invariant
            2 <= i <= n as int,
            forall|k: int| 2 <= k < i ==> (is_prime_number(k) ==> primes@.contains(k as i8)),
            forall|j: int| 0 <= j < primes.len() ==> is_prime_number(primes[j] as int),
            forall|j: int| 0 <= j < primes.len() ==> primes[j] as int < n as int,
            forall|j: int, k: int| 0 <= j < k < primes.len() ==> primes[j] as int < primes[k] as int,
            primes@.no_duplicates(),
        decreases (n as int) - i
    {
        if is_prime_exec(i) {
            primes.push(i as i8);
        }
        i = i + 1;
    }
    primes
}
// </vc-code>


}

fn main() {}