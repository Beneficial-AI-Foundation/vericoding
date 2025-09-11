// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn spec_fibfib(n: nat) -> (ret: nat)
    decreases n,
{
    if (n == 0) {
        0
    } else if (n == 1) {
        0
    } else if (n == 2) {
        1
    } else {
        spec_fibfib((n - 1) as nat) + spec_fibfib((n - 2) as nat) + spec_fibfib((n - 3) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn fibfib(x: u32) -> (ret: Option<u32>)

    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}