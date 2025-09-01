use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (ret:bool) {
    (n % divisor) == 0
}
// pure-end
// pure-end

spec fn is_prime(n: int) -> (ret:bool) {
    if n < 2 {
        false
    } else {
        (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k))
    }
}
// pure-end

// <vc-helpers>
// Helper function to check divisibility executably
fn is_divisible_exec(n: u32, divisor: u32) -> (ret: bool)
    requires
        divisor != 0,
    ensures
        ret == is_divisible(n as int, divisor as int),
{
    (n % divisor) == 0
}

// Executable function to check if a number is prime
fn is_prime_exec(n: u32) -> (ret: bool)
    ensures
        ret == is_prime(n as int),
{
    if n < 2 {
        return false;
    }
    
    let mut k: u32 = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k ==> !is_divisible(n as int, j),
    {
        if is_divisible_exec(n, k) {
            assert(is_divisible(n as int, k as int));
            assert(!is_prime(n as int));
            return false;
        }
        k = k + 1;
    }
    
    assert(forall|j: int| 2 <= j < n ==> !is_divisible(n as int, j));
    assert(is_prime(n as int));
    true
}
// </vc-helpers>

// <vc-spec>
fn prime_length(str: &[char]) -> (result: bool)
    // post-conditions-start
    ensures
        result == is_prime(str.len() as int),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = str.len();
    is_prime_exec(len as u32)
}
// </vc-code>

} // verus!
fn main() {}