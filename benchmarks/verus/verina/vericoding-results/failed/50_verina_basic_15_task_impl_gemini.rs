// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn contains_consecutive_numbers(a: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| {
            &&& 0 <= i < a.len() - 1
            &&& #[trigger] a[i] + 1 == a[(i + 1) as int]
        },
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let len = a.view().len();
    while i < len - 1
        invariant
            0 <= i <= len,
            forall|j: int| 0 <= j < i ==> a.view()[j] + 1 != a.view()[j + 1],
    {
        if a.view()[i] + 1 == a.view()[i + 1] {
            return true;
        }
        i = i + 1;
    }
    return false;
}
// </vc-code>

}
fn main() {}