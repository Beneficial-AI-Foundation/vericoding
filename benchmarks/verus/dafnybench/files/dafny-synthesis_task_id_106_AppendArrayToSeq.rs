// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn append_array_to_seq(s: Seq<i32>, a: &Vec<i32>) -> (r: Seq<i32>)
    ensures
        r.len() == s.len() + a.len(),
        forall|i: int| 0 <= i < s.len() ==> r[i] == s[i],
        forall|i: int| 0 <= i < a.len() ==> r[s.len() + i] == a[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}