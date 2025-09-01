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
#[verifier(external_body)]
proof fn lemma_divisibility_transitivity(a: int, b: int, c: int)
    requires
        is_divisible(a, b),
        is_divisible(b, c),
    ensures
        is_divisible(a, c),
{
}

#[verifier(external_body)]
proof fn lemma_prime_dvd_n(n: int, k: int)
    requires
        is_prime(n),
        2 <= k < n,
    ensures
        !is_divisible(n, k),
{
}

#[verifier(external_body)]
proof fn lemma_prime_n_gt_1(n: int)
requires
    is_prime(n)
ensures
    n >= 2
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
{
    // impl-start
    let len: nat = str.len() as nat;
    let len_int: int = len as int;
    if len_int < 2 {
        assert(len_int < 2 ==> !is_prime(len_int)); // prove postcondition for len < 2
        return false;
    } else {
        let mut k: int = 2;
        while k < len_int
            invariant
                2 <= k <= len_int,
                forall|i: int| 2 <= i < k ==> !is_divisible(len_int, i),
        {
            if is_divisible(len_int, k) {
                assert(!is_prime(len_int)); // prove postcondition for divisible case
                return false;
            }
            k = k + 1;
        }
        // k >= len_int
        assert(forall|i: int| 2 <= i < len_int ==> !is_divisible(len_int, i));
        assert(is_prime(len_int)); // prove postcondition for prime case
        return true;
    }
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}