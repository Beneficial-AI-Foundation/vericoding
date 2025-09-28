use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> #[trigger] (n % k) != 0,
    {
        if n % i == 0 {
            assert(2 <= i < n);
            assert(n % i == 0);
            assert(exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0);
            return true;
        }
        i = i + 1;
    }
    
    assert(i == n);
    assert(forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0);
    assert(!(exists|k: int| 2 <= k < n && #[trigger] (n % k) == 0));
    false
}
// </vc-code>

fn main() {}

}