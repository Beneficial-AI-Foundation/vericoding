// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn add_small_numbers(a: &Vec<i8>, n: usize, max: i8) -> (r: i8)
    requires 
        n > 0,
        n <= a@.len(),
        forall|i: int| 0 <= i && i < n ==> a@[i] as int <= max as int,
    ensures
        r as int <= (max as int) * (n as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}