use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
// </vc-spec>
// <vc-code>
{
    let mut i = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall |j: int| 2 <= j < i ==> #[trigger] (n % j) != 0
    {
        if n % i == 0 {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

fn main() {}

}