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
/* helper modified by LLM (iteration 2): simplified to direct recursive implementation without mutable references */
fn fibfib_impl(n: u32) -> (ret: Option<u32>)
    ensures
        ret.is_some() ==> spec_fibfib(n as nat) == ret.unwrap() as nat,
    decreases n,
{
    if n == 0 || n == 1 {
        Some(0)
    } else if n == 2 {
        Some(1)
    } else {
        let val1 = fibfib_impl(n - 1)?;
        let val2 = fibfib_impl(n - 2)?;
        let val3 = fibfib_impl(n - 3)?;
        val1.checked_add(val2)?.checked_add(val3)
    }
}
// </vc-helpers>

// <vc-spec>
fn fibfib(x: u32) -> (ret: Option<u32>)

    ensures
        ret.is_some() ==> spec_fibfib(x as nat) == ret.unwrap(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): replaced range-inclusive loop with simple range */
    fibfib_impl(x)
}
// </vc-code>

}
fn main() {}