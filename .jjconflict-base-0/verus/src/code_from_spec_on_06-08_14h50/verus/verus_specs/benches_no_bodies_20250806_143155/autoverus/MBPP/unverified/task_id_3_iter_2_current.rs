use vstd::prelude::*;

fn main() {}

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
    /* code modified by LLM (iteration 1): Added proof block and assertions to help verification */
    let mut i: u64 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
    {
        if n % i == 0 {
            proof {
                assert(is_divisible(n as int, i as int));
                assert(2 <= i as int < n);
                assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k));
            }
            return true;
        }
        i += 1;
    }
    
    proof {
        assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
        assert(!(exists|k: int| 2 <= k < n && is_divisible(n as int, k)));
    }
    false
}

} // verus!