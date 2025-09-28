use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
// </vc-spec>
// <vc-code>
{
    let mut is_prime = true;
    let mut k = 2;
    while k < n && is_prime
        invariant 2 <= k && k <= n
        invariant is_prime == (forall|m: int| 2 <= m < k ==> #[trigger] (n % m) != 0)
        decreases (n - k)
    {
        if n % k == 0 {
            is_prime = false;
        }
        k = k + 1;
    }
    is_prime
}
// </vc-code>

fn main() {
}

}