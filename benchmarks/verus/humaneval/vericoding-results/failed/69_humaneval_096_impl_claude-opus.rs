// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(num: int) -> bool {
    num >= 2 && forall|k: int| 2 <= k < num ==> #[trigger] (num % k) != 0
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed missing comma in lemma_prime_check requires clause */
spec fn is_prime_at(seq: Seq<i8>, i: int) -> bool {
    0 <= i < seq.len() && is_prime_number(seq[i] as int)
}

spec fn all_primes_below(seq: Seq<i8>, n: int) -> bool {
    forall|i: int| 0 <= i < seq.len() ==> is_prime_number(#[trigger] seq[i] as int) && (seq[i] as int) < n
}

spec fn sorted_seq(seq: Seq<i8>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> #[trigger] (seq[i] as int) < #[trigger] (seq[j] as int)
}

spec fn contains_all_primes_below(seq: Seq<i8>, n: int) -> bool {
    forall|p: int| 2 <= p < n && is_prime_number(p) ==> seq.contains(p as i8)
}

proof fn lemma_prime_check(n: i8, k: i8)
    requires
        2 <= k as int,
        k as int < n as int
    ensures
        is_prime_number(n as int) ==> (n as int) % (k as int) != 0
{
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
    /* code modified by LLM (iteration 5): Implementation remains unchanged */
    let mut result = Vec::new();
    let mut candidate: i8 = 2;
    
    while candidate < n
        invariant
            candidate as int >= 2,
            candidate as int <= n as int,
            forall|i: int| 0 <= i < result.len() ==> is_prime_number(#[trigger] result[i] as int),
            forall|i: int| 0 <= i < result.len() ==> #[trigger] (result[i] as int) < (candidate as int),
            forall|p: int| 2 <= p < (candidate as int) && is_prime_number(p) ==> result@.contains(p as i8),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] (result[i] as int) < #[trigger] (result[j] as int)
    {
        let mut is_prime = true;
        let mut divisor: i8 = 2;
        
        while divisor < candidate
            invariant
                2 <= divisor as int,
                divisor as int <= candidate as int,
                is_prime == forall|k: int| 2 <= k < (divisor as int) ==> (candidate as int) % k != 0
        {
            if candidate % divisor == 0 {
                is_prime = false;
            }
            divisor = divisor + 1;
        }
        
        if is_prime {
            result.push(candidate);
        }
        
        candidate = candidate + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}