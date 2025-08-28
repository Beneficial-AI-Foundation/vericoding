use vstd::prelude::*;

verus!{

// <vc-helpers>
spec fn is_odd(n: int) -> bool {
    n % 2 == 1
}
// </vc-helpers>

// <vc-spec>
fn choose_odd()
// </vc-spec>

// <vc-code>
fn choose_odd() -> (result: i32)
    ensures is_odd(result as int)
{
    1
}
// </vc-code>

}
fn main() {}