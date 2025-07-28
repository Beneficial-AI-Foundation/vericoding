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

proof fn lemma_divisor_not_prime(n: int, d: int)
    requires
        n >= 2,
        2 <= d < n,
        is_divisible(n, d),
    ensures
        !is_prime(n),
{
}
// pure-end

fn prime_length(str: &[char]) -> (result: bool)
    // post-conditions-start
    ensures
        result == is_prime(str.len() as int),
    // post-conditions-end
{
    let len = str.len();
    
    if len < 2 {
        return false;
    }
    
    let mut i: usize = 2;
    
    while i < len
        invariant
            2 <= i <= len,
            len == str.len(),
            forall|k: int| 2 <= k < i ==> !is_divisible(len as int, k),
        decreases len - i,
    {
        if len % i == 0 {
            proof {
                assert((len as int) % (i as int) == 0);
                assert(is_divisible(len as int, i as int));
                assert(len == str.len());
                assert(is_divisible(str.len() as int, i as int));
                lemma_divisor_not_prime(str.len() as int, i as int);
            }
            return false;
        }
        i = i + 1;
    }
    
    return true;
}

} // verus!
fn main() {}
