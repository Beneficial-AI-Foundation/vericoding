// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn abs_diff(x: int, y: int) -> nat {
    if x >= y { (x - y) as nat } else { (y - x) as nat }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn canyon_search(a: &Vec<i32>, b: &Vec<i32>) -> (result: u32)
    requires
        a.len() > 0,
        b.len() > 0,
        is_sorted(a@),
        is_sorted(b@),
    ensures
        exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && result as int == abs_diff(a[i], b[j]),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> result as int <= abs_diff(a[i], b[j]),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}