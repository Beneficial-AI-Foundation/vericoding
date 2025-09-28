// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_number(num: int) -> bool {
    num >= 2 && forall|k: int| 2 <= k < num ==> #[trigger] (num % k) != 0
}

// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed incomplete proof lemma and fixed is_prime_helper */
fn is_prime_helper(num: i8) -> (result: bool)
    requires num as int >= 2
    ensures result == is_prime_number(num as int)
{
    let mut k = 2i8;
    while k < num
        invariant
            2 <= k <= num,
            forall|i: int| 2 <= i < k ==> #[trigger] (num as int % i) != 0
        decreases num - k
    {
        if num % k == 0 {
            return false;
        }
        k = k + 1;
    }
    true
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
    /* code modified by LLM (iteration 5): fixed loop invariants and initialization */
    let mut result = Vec::new();
    
    if n < 2 {
        return result;
    }
    
    let mut candidate = 2i8;
    
    while candidate < n
        invariant
            2 <= candidate <= n,
            forall|i: int| 0 <= i < result.len() ==> is_prime_number(result[i] as int),
            forall|i: int| 0 <= i < result.len() ==> (result[i] as int) < n,
            forall|p: int| 2 <= p < (candidate as int) && is_prime_number(p) ==> result@.contains(p as i8),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> (result[i] as int) < (result[j] as int)
        decreases n - candidate
    {
        if is_prime_helper(candidate) {
            result.push(candidate);
        }
        candidate = candidate + 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}