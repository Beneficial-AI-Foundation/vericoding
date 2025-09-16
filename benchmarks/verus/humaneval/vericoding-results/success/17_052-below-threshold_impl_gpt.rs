// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_below_seq(s: Seq<i32>, t: i32) -> bool { forall|i: int| 0 <= i < s.len() ==> s[i] < t }
// </vc-helpers>

// <vc-spec>
fn below_threshold(l: &[i32], t: i32) -> (result: bool)

    ensures
        result == forall|i: int| 0 <= i < l.len() ==> l[i] < t,
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let mut all = true;
    while i < l.len()
        invariant
            0 <= i as int <= l.len() as int,
            all == forall|j: int| 0 <= j < i as int ==> l[j] < t,
        decreases l.len() - i
    {
        if !(l[i] < t) {
            all = false;
        }
        i += 1;
    }
    all
}
// </vc-code>

}
fn main() {}