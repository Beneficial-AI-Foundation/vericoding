use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
// </vc-spec>
// <vc-code>
{
    let mut k: int = 2;
    let mut ok: bool = true;
    while k < n
        invariant 2 <= k && k <= n && (ok <==> (forall|j: int| 2 <= j && j < k ==> #[trigger] (n % j) != 0))
        decreases n - k
    {
        if n % k == 0 {
            ok = false;
            proof {
                // witness that there is a divisor in [2, n)
                assert(2 <= k && k < n);
                assert(n % k == 0);
                assert(exists|j: int| j == k && 2 <= j && j < n && n % j == 0);
            }
            k = n;
        } else {
            proof {
                // from invariant and n % k != 0, extend the forall to k+1
                assert(ok <==> (forall|j: int| 2 <= j && j < k ==> #[trigger] (n % j) != 0));
                assert(n % k != 0);
                // show: ok <==> forall j in [2, k+1) n%j != 0
                // Left-to-right: if ok then forall j<k holds, and n%k != 0, so forall j<k+1 holds.
                // Right-to-left: if forall j<k+1 holds then in particular forall j<k holds, so ok holds.
                assert((ok ==> (forall|j: int| 2 <= j && j < (k + 1) ==> #[trigger] (n % j) != 0)) &&
                       (((forall|j: int| 2 <= j && j < (k + 1) ==> #[trigger] (n % j) != 0)) ==> ok));
            }
            k = k + 1;
        }
    }
    ok
}
// </vc-code>

fn main() {
}

}