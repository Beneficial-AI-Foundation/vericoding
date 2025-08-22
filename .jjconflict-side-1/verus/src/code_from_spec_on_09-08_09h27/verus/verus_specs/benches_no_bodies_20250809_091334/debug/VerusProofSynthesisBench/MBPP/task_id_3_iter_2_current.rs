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
    let mut i: u64 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
        /* code modified by LLM (iteration 1): added decreases clause to show loop terminates */
        decreases n - i
    {
        if n % i == 0 {
            return true;
        }
        i = i + 1;
    }
    false
}

} // verus!

fn main() {}