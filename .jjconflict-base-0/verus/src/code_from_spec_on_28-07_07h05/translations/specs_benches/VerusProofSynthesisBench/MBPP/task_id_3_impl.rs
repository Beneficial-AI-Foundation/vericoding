use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}
// pure-end

fn is_non_prime(n: u64) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
    // post-conditions-end
{
    let mut k = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k ==> !is_divisible(n as int, j),
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases n - k
    {
        if n % k == 0 {
            /* code modified by LLM (iteration 1): added assertion to help prove postcondition when returning true */
            assert(is_divisible(n as int, k as int));
            assert(2 <= k < n);
            return true;
        }
        k = k + 1;
    }
    /* code modified by LLM (iteration 1): added assertion to prove no divisors exist when returning false */
    assert(k == n);
    assert(forall|j: int| 2 <= j < n ==> !is_divisible(n as int, j));
    return false;
}

} // verus!

fn main() {}