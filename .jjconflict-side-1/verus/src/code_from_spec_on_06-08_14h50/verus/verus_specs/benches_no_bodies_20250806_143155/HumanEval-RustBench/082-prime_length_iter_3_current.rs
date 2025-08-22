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
    let len = str.len();
    
    /* code modified by LLM (iteration 1): removed int cast, work with usize in executable code */
    if len < 2 {
        return false;
    }
    
    let mut i: usize = 2;
    while i < len
        invariant
            2 <= i <= len,
            /* code modified by LLM (iteration 1): cast to int for spec function in invariant */
            forall|k: int| 2 <= k < i ==> !is_divisible(len as int, k),
        /* code modified by LLM (iteration 1): added decreases clause for loop termination */
        decreases len - i
    {
        if len % i == 0 {
            return false;
        }
        i += 1;
    }
    
    true
}

} // verus!
fn main() {}