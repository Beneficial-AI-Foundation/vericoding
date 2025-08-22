use vstd::prelude::*;

fn main() {
    let result = prime_num(7);
    println!("7 is prime: {}", result);
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
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
        decreases n - i,
    {
        if n % i == 0 {
            return false;
        }
        i = i + 1;
    }
    
    true
}

} // verus!