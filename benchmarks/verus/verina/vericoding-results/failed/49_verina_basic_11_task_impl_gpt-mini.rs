// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn mod_lt(n: nat, d: nat)
    requires d > 0
    ensures n % d < d
{ }
// </vc-helpers>

// <vc-spec>
fn last_digit(n: nat) -> (result: nat)
    ensures
        result < 10,
        result == n % 10,
// </vc-spec>
// <vc-code>
{
    let r: nat = n % 10;
    proof {
        mod_lt(n, 10);
    }
    r
}
// </vc-code>

}
fn main() {}