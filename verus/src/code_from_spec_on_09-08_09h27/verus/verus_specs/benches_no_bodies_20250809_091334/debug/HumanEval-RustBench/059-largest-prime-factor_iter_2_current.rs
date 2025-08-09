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
    if num == 2 {
        return true;
    }
    
    let mut i = 2;
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < num
        invariant
            2 <= i <= num,
            forall|j: int| 2 <= j < i ==> (#[trigger] ((num as int) % j)) != 0,
        decreases num - i,
    {
        if num % i == 0 {
            return false;
        }
        i = i + 1;
    }
    true
}

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
    let mut current = n;
    let mut largest_factor = 2;
    
    let mut factor = 2;
    /* code modified by LLM (iteration 1): added decreases clause for outer loop termination */
    while factor * factor <= current
        invariant
            2 <= factor,
            2 <= current <= n,
            current >= 2,
            spec_prime(largest_factor as int),
            largest_factor <= n,
        decreases current,
    {
        /* code modified by LLM (iteration 1): added decreases clause for inner loop termination */
        while current % factor == 0
            invariant
                2 <= factor,
                2 <= current <= n,
                spec_prime(largest_factor as int),
                largest_factor <= n,
            decreases current,
        {
            largest_factor = factor;
            current = current / factor;
        }
        factor = factor + 1;
    }
    
    if current > 1 {
        largest_factor = current;
    }
    
    largest_factor
}

}
fn main() {}