// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i8>, key: i8) -> (result: i8)
    ensures
        (result == -1 || (result >= 0 && (result as int) < (a@.len() as int))),
        result != -1 ==> (a@[result as int] == (key as int) && forall|i: int| 0 <= i < (result as int) ==> a@[i] != (key as int)),
        result == -1 ==> forall|i: int| 0 <= i < (a@.len() as int) ==> a@[i] != (key as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}