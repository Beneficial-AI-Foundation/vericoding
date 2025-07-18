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

/* code modified by LLM (iteration 4): Fixed type usage - use usize for executable code and cast to int only for specifications */
fn prime_length(str: &[char]) -> (result: bool)
    ensures
        result == is_prime(str.len() as int),
{
    let len = str.len();
    
    if len < 2 {
        return false;
    }
    
    let mut k: usize = 2;
    while k < len
        invariant
            2 <= k <= len &&
            forall|i: int| 2 <= i < k ==> !is_divisible(len as int, i)
    {
        if len % k == 0 {
            return false;
        }
        k += 1;
    }
    
    return true;
}

} // verus!
fn main() {}