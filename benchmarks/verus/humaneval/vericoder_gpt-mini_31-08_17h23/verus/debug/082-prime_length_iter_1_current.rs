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
// No helpers needed for this proof.
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
    let n: int = str.len() as int;
    if n < 2 {
        return false;
    }
    let mut k: int = 2;
    let mut no_div: bool = true;
    while k < n
        invariant 2 <= k <= n
        invariant no_div == (forall|i: int| 2 <= i < k ==> !#[trigger]is_divisible(n, i))
    {
        no_div = no_div && !is_divisible(n, k);
        k = k + 1;
    }
    proof {
        assert(!(k < n));
        assert(k >= n);
        assert(k <= n);
        assert(k == n);
        assert(no_div == (forall|i: int| 2 <= i < n ==> !#[trigger]is_divisible(n, i)));
    }
    no_div
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}