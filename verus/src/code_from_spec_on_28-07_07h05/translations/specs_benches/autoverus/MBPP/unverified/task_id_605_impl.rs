use vstd::prelude::*;

fn main() {}

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
    /* code modified by LLM (iteration 2): updated invariant to properly capture the relationship between finding a divisor and the postcondition */
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
        decreases n - i,
    {
        /* code modified by LLM (iteration 2): added assertion to help verification understand the divisibility relationship */
        if n % i == 0 {
            assert(is_divisible(n as int, i as int));
            assert(2 <= i < n);
            assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k));
            assert(!(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)));
            return false;
        }
        i = i + 1;
    }
    /* code modified by LLM (iteration 2): added assertion to help verification understand that no divisors were found */
    assert(i == n);
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
    return true;
}

} // verus!