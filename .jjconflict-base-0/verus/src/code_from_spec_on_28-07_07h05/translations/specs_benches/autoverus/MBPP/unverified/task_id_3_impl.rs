use vstd::prelude::*;

fn main() {}

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

//IMPL is_non_prime
fn is_non_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
{
    let mut i: u64 = 2;
    /* code modified by LLM (iteration 1): updated loop invariant to track that no divisors have been found so far */
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
        decreases n - i,
    {
        if n % i == 0 {
            /* code modified by LLM (iteration 1): added assertion to help prove postcondition when returning true */
            assert(is_divisible(n as int, i as int));
            assert(2 <= i < n);
            return true;
        }
        i = i + 1;
    }
    /* code modified by LLM (iteration 1): added assertion to help prove postcondition when returning false */
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
    return false;
}

} // verus!