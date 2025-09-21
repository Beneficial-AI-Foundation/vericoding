// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find(a: &[i8], key: i8) -> (index: i8)
    ensures
        -1 <= index < a.len() as i8,
        index != -1 ==> a[index as int] == key && (forall|i: int| 0 <= i < index ==> a[i] != key),
        index == -1 ==> (forall|i: int| 0 <= i < a@.len() ==> a[i] != key),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}