use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

fn is_non_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
{
    let mut i: u64 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases n - i
    {
        if n % i == 0 {
            /* code modified by LLM (iteration 1): added assertion to help prove postcondition when returning true */
            assert(is_divisible(n as int, i as int));
            assert(2 <= i < n);
            return true;
        }
        i = i + 1;
    }
    /* code modified by LLM (iteration 1): added assertion to prove postcondition when returning false */
    assert(i == n);
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
    false
}

} // verus!

fn main() {}