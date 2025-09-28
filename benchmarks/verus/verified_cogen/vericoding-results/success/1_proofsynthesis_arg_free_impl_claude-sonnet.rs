// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
spec fn is_odd(x: int) -> bool { x % 2 == 1 }

fn get_odd_number() -> (result: i32)
    ensures is_odd(result as int)
{
    1
}
// </vc-helpers>

// <vc-spec>
fn choose_odd()
// </vc-spec>
// <vc-code>
-> (result: i32)
    ensures is_odd(result as int)
{
    get_odd_number()
}
// </vc-code>

}
fn main() {}