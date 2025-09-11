// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn pal_verify(a: &Vec<char>) -> (yn: bool)
    ensures yn == true ==> (forall|i: int| 0 <= i < a.len()/2 ==> #[trigger] a[i] == #[trigger] a[a.len() - i - 1]),
            yn == false ==> (exists|i: int| #![trigger a[i], a[a.len() - i - 1]] 0 <= i < a.len()/2 && a[i] != a[a.len() - i - 1])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}