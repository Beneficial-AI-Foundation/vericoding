use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
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
    let mut i = 2 as int;
    let mut found = false;
    proof {
        while i < n as int
            invariant
                2 <= i <= n as int,
                n as int >= 2,
                i <= n as int,
                found == exists|k: int| 2 <= k < i && #[trigger] (n as int % k) == 0,
                forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k != 0),
        {
            let remainder = n as int % i;
            if remainder == 0 {
                found = true;
            }
            i = i + 1;
            if remainder == 0 {} else {
                assert(forall|k: int| 2 <= k < i ==> #[trigger] (n as int % k != 0));
            }
        }
    }
    found
}
// </vc-code>

fn main() {}
}