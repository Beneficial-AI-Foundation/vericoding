use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0)
// </vc-spec>
// <vc-code>
{
    let mut k: int = 2;
    let mut res: bool = false;
    // Loop invariant: k stays between 2 and n, and res iff there exists a divisor in [2, k)
    while k < n && !res
        invariant 2 <= k <= n
        invariant { res <==> (exists|j: int| 2 <= j < k && #[trigger] ((n % j) == 0)) }
        decreases n - k
    {
        if n % k == 0 {
            res = true;
        }
        k = k + 1;
    }

    // Prove the postcondition: res <==> exists j in [2, n) with n % j == 0
    proof {
        assert(2 <= k && k <= n);
        assert(res <==> (exists|j: int| 2 <= j < k && (n % j) == 0));
        assert(!(k < n && !res));
        assert(k >= n || res);

        if res {
            assert(exists|j: int| 2 <= j < k && (n % j) == 0);
            // Since k <= n, j < k implies j < n
            assert(exists|j: int| 2 <= j < n && (n % j) == 0);
        } else {
            assert(!(exists|j: int| 2 <= j < k && (n % j) == 0));
            assert(k >= n);
            // k >= n and k <= n implies k == n
            assert(k == n);
            assert(!(exists|j: int| 2 <= j < n && (n % j) == 0));
        }
    }

    res
}
// </vc-code>

fn main() {}

}