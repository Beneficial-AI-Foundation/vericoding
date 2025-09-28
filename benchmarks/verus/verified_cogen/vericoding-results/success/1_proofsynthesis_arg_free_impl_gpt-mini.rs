// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn odd() -> int { 1 }
spec fn is_odd(n: int) -> bool { n % 2 == 1 }
// </vc-helpers>

// <vc-spec>
fn choose_odd()
// </vc-spec>
// <vc-code>
{
    proof {
        let x: int = odd();
        assert(is_odd(x));
    }
}
// </vc-code>

}
fn main() {}