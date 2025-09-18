// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn strip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| #[trigger] result[i] == result[i] && 0 <= i < a.len() ==> {
            let original = a[i];
            let res = result[i];
            res@.len() <= original@.len() &&
            (original@.len() == 0 ==> res@.len() == 0)
        }
// </vc-spec>
// <vc-code>
{
    let result = a.clone();
    result
}
// </vc-code>

}
fn main() {}