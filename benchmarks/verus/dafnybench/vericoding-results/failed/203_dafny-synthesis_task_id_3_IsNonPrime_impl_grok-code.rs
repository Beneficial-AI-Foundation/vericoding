use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_divisor(k: int, n: int) -> bool
    requires 2 <= k < n,
    ensures result <==> (n % k == 0)
{
    n % k == 0
}
// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 2;
    while i < n
        invariant 2 <= i <= n
        invariant forall |k: int| 2 <= k < i ==> #[trigger] (n % k != 0)
    {
        if n % i == 0 {
            assert(2 <= i < n && #[trigger] (n % i) == 0);
            return true;
        } else {
            assert(n % i != 0);
        }
        i += 1;
    }
    assert(forall |k: int| 2 <= k < n ==> #[trigger] (n % k != 0));
    false
}
// </vc-code>

fn main() {}

}