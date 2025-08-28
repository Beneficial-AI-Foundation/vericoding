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
proof fn prove_prime(n: int)
    requires
        2 <= n,
    ensures
        is_prime(n) == (forall|k: int| 2 <= k < n ==> !is_divisible(n, k)),
{
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
fn prime_length(str: &[char]) -> (result: bool)
    ensures
        result == is_prime(str.len() as int),
{
    let len = str.len() as int;
    if len < 2 {
        return false;
    }
    let mut k = 2;
    while k < len
        invariant
            2 <= k <= len,
            forall|j: int| 2 <= j < k ==> !is_divisible(len, j),
    {
        if is_divisible(len, k) {
            return false;
        }
        k = k + 1;
    }
    true
}
// </vc-code>

} // verus!
fn main() {}