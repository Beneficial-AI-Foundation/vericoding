use vstd::prelude::*;

fn main() {
    // Example usage
    let is_prime_5 = prime_num(5);
    println!("5 is prime: {}", is_prime_5);
}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

fn prime_num(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
{
    let mut i: u64 = 2;
    
    /* code modified by LLM (iteration 1): added decreases clause and fixed postcondition proof */
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
        decreases n - i,
    {
        if n % i == 0 {
            /* code modified by LLM (iteration 1): added assertion to prove postcondition when returning false */
            assert(is_divisible(n as int, i as int));
            assert(2 <= i < n);
            assert(!(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)));
            return false;
        }
        i = i + 1;
    }
    
    /* code modified by LLM (iteration 1): added assertion to prove postcondition when returning true */
    assert(i == n);
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
    true
}

} // verus!