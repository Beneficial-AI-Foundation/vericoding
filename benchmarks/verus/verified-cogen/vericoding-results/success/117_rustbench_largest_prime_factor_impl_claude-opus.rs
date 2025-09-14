// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime_pred(n: u32) -> bool {
    forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn largest_prime_factor(n: u32) -> (result: u32)
    requires
        2 <= n <= u32::MAX - 1,
    ensures
        1 <= result <= n,
        result == 1 || (result > 1 && is_prime_pred(result))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Added trigger annotation to forall in invariant */
    let mut largest = 1u32;
    let mut k = 2u32;
    
    while k <= n
        invariant
            2 <= n <= u32::MAX - 1,
            2 <= k <= n + 1,
            1 <= largest <= n,
            largest == 1 || (largest > 1 && is_prime_pred(largest)),
            forall|j: int| 2 <= j < k && #[trigger] (n as int % j) == 0 && is_prime_pred(j as u32) ==> j <= largest,
        decreases n - k + 1,
    {
        if n % k == 0 {
            let mut is_prime = true;
            let mut i = 2u32;
            
            while i < k
                invariant
                    2 <= i <= k,
                    2 <= k <= n,
                    is_prime <==> forall|m: int| 2 <= m < i ==> #[trigger] (k as int % m) != 0,
                decreases k - i,
            {
                if k % i == 0 {
                    is_prime = false;
                }
                i = i + 1;
            }
            
            if is_prime {
                largest = k;
            }
        }
        k = k + 1;
    }
    
    largest
}
// </vc-code>

}
fn main() {}