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
fn choose_odd() -> (result: int)
    ensures
        is_odd(result)
{
    3
}
// </vc-code>

}
fn main() {}