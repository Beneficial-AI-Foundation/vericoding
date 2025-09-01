use vstd::prelude::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    // impl-start
    let mut i: u32 = 2;
    while i < n {
        invariant 2 <= i && i <= n;
        invariant !(exists |k: int| 2 <= k < i as int && #[trigger] (n as int % k) == 0);
        if n % i == 0 {
            proof {
                let k: int = i as int;
                assert(2 <= k);
                assert(k < n as int);
                assert(#[trigger] (n as int % k) == 0);
                assert(exists |kk: int| 2 <= kk < n as int && #[trigger] (n as int % kk) == 0);
            }
            return true;
        }
        i += 1;
    }
    proof {
        assert(!(exists |k: int| 2 <= k < n as int && #[trigger] (n as int % k) == 0));
    }
    false
    // impl-end
}
// </vc-code>

fn main() {}
}