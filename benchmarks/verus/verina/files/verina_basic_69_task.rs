// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn linear_search(a: &Vec<i8>, e: i8) -> (result: usize)
    requires exists|i: int| 0 <= i < a@.len() && a@[i] == e as int,
    ensures
        result < a@.len(),
        a@[result as int] == e as int,
        forall|k: int| 0 <= k < result ==> a@[k] != e as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}