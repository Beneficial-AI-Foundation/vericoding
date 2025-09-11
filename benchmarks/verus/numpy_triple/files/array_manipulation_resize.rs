// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn resize<T>(a: Vec<T>, new_size: usize) -> (result: Vec<T>)
    ensures
        result.len() == new_size,
        forall|i: int| 0 <= i < new_size ==> {
            if i < a.len() {
                result[i] == a[i]
            } else if a.len() > 0 {
                result[i] == a[(i % a.len() as int) as int]
            } else {
                true
            }
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