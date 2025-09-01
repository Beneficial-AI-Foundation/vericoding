use vstd::prelude::*;

verus! {

// <vc-helpers>

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
let mut i: u32 = 2;
    let mut found: bool = false;
    while i < n && !found
        invariant
            n >= 2,
            2 <= i <= n as int,
            found == exists|k: int| 2 <= k < i as int && #[trigger] ((n as int % k) == 0),
            !found ==> forall|k: int| 2 <= k < i as int ==> #[trigger] ((n as int % k) != 0),
    {
        let remainder: int = n as int % (i as int);
        if remainder == 0 {
            found = true;
        }
        i = i + 1;
    }
    found
// </vc-code>

fn main() {}
}