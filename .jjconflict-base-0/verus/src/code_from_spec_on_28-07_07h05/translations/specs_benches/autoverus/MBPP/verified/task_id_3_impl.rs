use vstd::prelude::*;

fn main() {
    println!("Prime checker implementation");
}

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
        decreases n - i,
    {
        if n % i == 0 {
            /* code modified by LLM (iteration 1): added assertion to establish witness for existential */
            assert(is_divisible(n as int, i as int));
            assert(2 <= i < n);
            return true;
        }
        i = i + 1;
    }
    /* code modified by LLM (iteration 1): added assertion to prove no divisor exists */
    assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k));
    false
}

} // verus!