use vstd::prelude::*;

verus! {

spec fn is_divisible(n: int, divisor: int) -> (result: bool) {
    (n % divisor) == 0
}
// pure-end

// <vc-helpers>
proof fn lemma_divisible_self(n: int)
    requires
        n > 0,
    ensures
        is_divisible(n, n),
{
    // Verus can automatically prove that n % n == 0 for n > 0
}
// </vc-helpers>

// <vc-spec>
fn prime_num(n: u64) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn prime_num(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
{
    let mut i: u64 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> !is_divisible(n as int, k),
    {
        if (n % i) == 0 {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

} // verus!

fn main() {}