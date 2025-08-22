use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (ret:bool) {
    (n % divisor) == 0
}
// pure-end

spec fn is_prime(n: int) -> (ret:bool) {
    if n < 2 {
        false
    } else {
        (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k))
    }
}
// pure-end

fn prime_length(str: &[char]) -> (result: bool)
    // post-conditions-start
    ensures
        result == is_prime(str.len() as int),
    // post-conditions-end
{
    let n = str.len();
    
    if n < 2 {
        return false;
    }
    
    let mut i = 2;
    /* code modified by LLM (iteration 1): strengthened invariant to properly handle both the case where a divisor is found and the case where no divisor exists */
    while i < n
        invariant 
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> #[trigger] ((n as int) % k) != 0,
        decreases n - i,
    {
        if n % i == 0 {
            /* code modified by LLM (iteration 1): added assertion to establish that finding a divisor proves the number is not prime */
            assert(is_divisible(n as int, i as int));
            assert(2 <= i < n);
            assert(!is_prime(n as int));
            return false;
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to establish that no divisors were found, proving the number is prime */
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
    assert(is_prime(n as int));
    true
}

} // verus!
fn main() {}