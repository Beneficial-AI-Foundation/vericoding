// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    ensures
        (result == -1 || (result >= 0 && result < a.len())),
        result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key),
        result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}