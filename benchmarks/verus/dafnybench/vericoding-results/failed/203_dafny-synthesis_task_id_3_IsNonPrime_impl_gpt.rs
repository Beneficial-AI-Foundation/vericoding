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
    let mut k: int = 2;
    while k < n
        invariant
            n >= 2,
            2 <= k <= n,
            forall|j: int| 2 <= j && j < k ==> #[trigger] (n % j) != 0,
        decreases n - k
    {
        if n % k == 0 {
            proof {
                assert(2 <= k && k < n && n % k == 0);
                assert(exists|k2: int| 2 <= k2 && k2 < n && #[trigger] (n % k2) == 0) by {
                    assert(2 <= k && k < n && n % k == 0);
                }
            }
            return true;
        }
        k = k + 1;
        assert(k <= n);
    }
    assert(!(k < n));
    assert(k <= n);
    assert(k == n);
    proof {
        assert(forall|j: int| 2 <= j && j < n ==> #[trigger] (n % j) != 0) by {
            assert(k == n);
            assert(forall|j: int| 2 <= j && j < k ==> #[trigger] (n % j) != 0);
        }
        assert(!exists|j: int| 2 <= j && j < n && (n % j) == 0);
    }
    false
}
// </vc-code>

fn main() {}

}