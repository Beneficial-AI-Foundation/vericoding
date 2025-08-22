use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (result: bool) {
    (n % divisor) == 0
}
// pure-end

fn prime_num(n: u64) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
    // post-conditions-end
{
    let mut i: u64 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
        decreases n - i
    {
        if n % i == 0 {
            /* code modified by LLM (iteration 1): Added assertion to prove postcondition when returning false */
            assert(is_divisible(n as int, i as int));
            assert(2 <= i < n);
            assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k));
            return false;
        }
        i = i + 1;
    }
    /* code modified by LLM (iteration 1): Added assertion to prove postcondition when returning true */
    assert(i == n);
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
    return true;
}

} // verus!

fn main() {}