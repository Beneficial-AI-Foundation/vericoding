use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_non_prime(n: u32) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 2;
    while i < n
        invariant
            2 <= i <= n,
            forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k) != 0,
    {
        if n % i == 0 {
            assert(2 <= i < n);
            assert(n as int % i as int == 0);
            return true;
        }
        i = i + 1;
    }
    
    assert(i == n);
    assert(forall|k: int| 2 <= k < n ==> #[trigger] (n as int % k) != 0);
    false
}
// </vc-code>

fn main() {}
}