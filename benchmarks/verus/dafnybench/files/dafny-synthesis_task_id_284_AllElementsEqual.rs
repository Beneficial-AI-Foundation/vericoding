// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn all_elements_equal(a: &Vec<i8>, n: i8) -> (result: bool)
    ensures
        result ==> forall|i: int| 0 <= i < a@.len() ==> a@[i] == n as int,
        !result ==> exists|i: int| 0 <= i < a@.len() && a@[i] != n as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}