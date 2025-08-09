use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (ret:bool) {
    (n % divisor) == 0
}
// pure-end

spec fn is_prime(n: int) -> (ret:bool) {
    if n < 2 {
        false
    } else {
        (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k))
    }
}
// pure-end

fn prime_length(str: &[char]) -> (result: bool)
    // post-conditions-start
    ensures
        result == is_prime(str.len() as int),
    // post-conditions-end
{
    /* code modified by LLM (iteration 1): Fixed type usage - use usize for executable code and convert to int for spec */
    let n = str.len();
    
    if n < 2 {
        return false;
    }
    
    let mut i: usize = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
    {
        if n % i == 0 {
            return false;
        }
        i = i + 1;
    }
    
    true
}

} // verus!
fn main() {}