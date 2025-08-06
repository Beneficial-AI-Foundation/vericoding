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
    let mut i = 2u64;
    
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
    {
        if n % i == 0 {
            assert(is_divisible(n as int, i as int));
            assert(2 <= i as int < n as int);
            return true;
        }
        i += 1;
    }
    
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
    false
}

} // verus!

fn main() {}