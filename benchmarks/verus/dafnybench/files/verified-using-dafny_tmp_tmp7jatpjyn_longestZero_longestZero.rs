// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn get_size(i: int, j: int) -> int {
    j - i + 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest_zero(a: &Vec<i8>) -> (result: (usize, usize))
    requires 
        1 <= a@.len()
    ensures 
        result.0 <= a@.len(),
        result.1 < a@.len(),
        result.1 + result.0 <= a@.len(),
        forall |i: int| result.1 as int <= i < (result.1 as int + result.0 as int) ==> a@[i] == 0,
        forall |i: int, j: int| {
            0 <= i < j < a@.len() && get_size(i, j) > (result.0 as int)
            ==> exists |k: int| i <= k <= j && a@[k] != 0
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}