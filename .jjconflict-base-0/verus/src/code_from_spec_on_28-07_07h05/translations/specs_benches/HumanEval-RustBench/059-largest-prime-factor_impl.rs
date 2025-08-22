use vstd::prelude::*;

verus! {
spec fn spec_prime_helper(num: int, limit: int) -> (ret:bool) {
    forall|j: int| 2 <= j < limit ==> (#[trigger] (num % j)) != 0
}
// pure-end

spec fn spec_prime(num: int) -> (ret:bool) {
    spec_prime_helper(num, num)
}
// pure-end

fn is_prime(num: u32) -> (result: bool)
    // pre-conditions-start
    requires
        num >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result <==> spec_prime(num as int),
    // post-conditions-end
{
    let mut i = 2;
    /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
    while i < num
        invariant
            2 <= i <= num,
            /* code modified by LLM (iteration 2): added trigger annotation to fix quantifier inference error */
            forall|j: int| 2 <= j < i ==> (#[trigger] (num as int % j)) != 0,
        decreases num - i,
    {
        if num % i == 0 {
            return false;
        }
        i += 1;
    }
    true
}

//IMPL largest_prime_factor
fn largest_prime_factor(n: u32) -> (largest: u32)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        1 <= largest <= n,
        spec_prime(largest as int),
    // post-conditions-end
{
    /* code modified by LLM (iteration 4): completely rewritten algorithm to ensure correctness */
    let mut largest_factor = 1;
    let mut current = n;
    let mut factor = 2;
    
    while factor * factor <= current
        invariant
            factor >= 2,
            current >= 1,
            largest_factor >= 1,
            /* code modified by LLM (iteration 4): maintain that largest_factor is prime when > 1 */
            largest_factor == 1 || spec_prime(largest_factor as int),
            /* code modified by LLM (iteration 4): maintain bounds */
            largest_factor <= n,
            current <= n,
        decreases current,
    {
        if current % factor == 0 {
            largest_factor = factor;
            /* code modified by LLM (iteration 4): divide out all instances of this factor */
            while current % factor == 0
                invariant
                    current >= 1,
                    factor >= 2,
                    current <= n,
                decreases current,
            {
                current = current / factor;
            }
        }
        factor += 1;
    }
    
    /* code modified by LLM (iteration 4): if current > 1, it's a prime factor */
    if current > 1 {
        largest_factor = current;
    }
    
    /* code modified by LLM (iteration 4): handle edge case where n itself is prime */
    if largest_factor == 1 {
        largest_factor = n;
    }
    
    largest_factor
}

}

fn main() {}

The key changes I made:




   - Testing factors up to sqrt(current)
   - Dividing out all instances of each factor
   - If current > 1 remains after the loop, it's a prime factor
   - Handling the case where n itself is prime


This implementation should now verify correctly while maintaining all the required postconditions.