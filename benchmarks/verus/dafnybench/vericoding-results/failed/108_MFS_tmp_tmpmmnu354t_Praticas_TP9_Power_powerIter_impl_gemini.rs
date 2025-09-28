// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n-1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): refactored spec function to be recursive and added proof helpers. */
spec fn is_power_in_i32_range(b: int, n: nat) -> bool
    decreases n
{
    if n == 0 {
        true
    } else {
        (i32::MIN <= power(b, n) <= i32::MAX) && is_power_in_i32_range(b, (n-1) as nat)
    }
}

proof fn power_unfold(x: int, n: nat)
    requires n > 0
    ensures power(x, n) == x * power(x, (n - 1) as nat)
{
}

proof fn is_power_in_range_propa(b: int, n: nat, i: nat)
    requires
        i <= n,
        is_power_in_i32_range(b, n),
    ensures
        is_power_in_i32_range(b, i),
    decreases n - i
{
    if i < n {
        is_power_in_range_propa(b, (n-1) as nat, i);
    }
}

proof fn is_power_in_range_unfold(b: int, i: nat)
    requires
        i > 0,
        is_power_in_i32_range(b, i),
    ensures
        i32::MIN <= power(b, i) <= i32::MAX,
{
}
// </vc-helpers>

// <vc-spec>
fn power_iter(b: i32, n: u32) -> (p: i32)
    ensures p as int == power(b as int, n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added proof block to prove absence of overflow. */
    let mut p: i32 = 1;
    let mut i: u32 = 0;

    while i < n
        invariant
            i <= n,
            p as int == power(b as int, i as nat),
            is_power_in_i32_range(b as int, n as nat),
        decreases n - i
    {
        proof {
            power_unfold(b as int, (i + 1) as nat);
            is_power_in_range_propa(b as int, n as nat, (i + 1) as nat);
            is_power_in_range_unfold(b as int, (i + 1) as nat);
        }
        p = p * b;
        i = i + 1;
    }
    
    p
}
// </vc-code>

}
fn main() {}