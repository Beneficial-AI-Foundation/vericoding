use vstd::prelude::*;

verus! {

// <vc-helpers>
// <vc-helpers>
use vstd::prelude::*;

// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum(n: u32) -> (s: u32)
    requires n >= 0
    ensures s == n * (n + 1) / 2
// </vc-spec>
// <vc-code>
{
    let mut sum: u32 = 0;
    let mut k: u32 = 1;
    while k <= n
        invariant 1 <= k as int && k as int <= (n as int) + 1;
        invariant sum as int == ((k as int - 1) * k as int) / 2;
    {
        assert((sum as int) + (k as int) <= (u32::MAX as int));
        assert((k as int) + 1 <= (u32::MAX as int));
        sum = sum.checked_add(k).unwrap();
        k = k.checked_add(1).unwrap();
    }
    sum
}
// </vc-code>

fn main() {}

}