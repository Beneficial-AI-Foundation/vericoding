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
// (no helpers needed)
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
    let n = str.len();
    if n < 2 {
        return false;
    }
    let mut i: usize = 2;
    while i < n
        invariant (2 as int) <= (i as int) && (i as int) <= (str.len() as int)
        invariant forall|k: int| 2 <= k && k < (i as int) ==> ((str.len() as int) % k != 0)
        decreases n - i
    {
        if n % i == 0 {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

} // verus!
fn main() {}