// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_prime(n: int) -> bool {
    n > 1 && forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0
}

spec fn power_of_2_factor(n: int, current: int) -> int
    recommends n > 0 && current > 0
    decreases current
    when current > 0
{
    if current % 2 != 0 { 1 }
    else { 2 * power_of_2_factor(n, current / 2) }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn largest_prime_factor(n: i8) -> (result: i8)
    requires 
        n as int > 1,
        !is_prime(n as int),
    ensures 
        result as int > 1,
        (n as int) % (result as int) == 0,
        forall|k: int| k > result as int && (n as int) % k == 0 ==> !is_prime(k),
        is_prime(result as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed syntax error - replaced chained comparison with && */
    let mut largest = 1i8;
    let mut i = 2i8;
    
    while i <= n
        invariant
            2 <= i <= n + 1,
            1 <= largest < i,
            largest > 1 ==> is_prime(largest as int),
            largest > 1 ==> (n as int) % (largest as int) == 0,
            forall|k: int| largest as int < k && k < i as int ==> (n as int) % k == 0 ==> !is_prime(k),
        decreases n - i + 1
    {
        if n % i == 0 {
            let mut is_prime_i = true;
            let mut j = 2i8;
            
            while j < i
                invariant
                    2 <= j <= i,
                    2 <= i <= n,
                    is_prime_i <==> forall|k: int| 2 <= k && k < j as int ==> (i as int) % k != 0,
                decreases i - j
            {
                if i % j == 0 {
                    is_prime_i = false;
                }
                j = j + 1;
            }
            
            if is_prime_i {
                largest = i;
            }
        }
        i = i + 1;
    }
    
    largest
}
// </vc-code>


}

fn main() {}