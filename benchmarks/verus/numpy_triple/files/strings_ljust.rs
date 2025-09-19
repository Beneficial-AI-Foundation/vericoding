// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn ljust(a: Vec<String>, width: u8, fillchar: char) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() == if a[i]@.len() >= width as nat { a[i]@.len() } else { width as nat },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() >= width as nat ==> #[trigger] result[i]@ == a[i]@,
        forall|i: int| 0 <= i < a.len() && a[i]@.len() < width as nat ==> {
            &&& #[trigger] result[i]@.len() == width as nat
            &&& result[i]@.subrange(0, a[i]@.len() as int) == a[i]@
        },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() == 0 ==> #[trigger] result[i]@.len() == width as nat
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}