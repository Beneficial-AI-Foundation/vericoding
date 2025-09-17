// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn affine(x: int, shift: int, scale: int) -> int {
    if scale > 0 { (x + shift) / scale } else { 0 }
}

spec fn affine_seq(s: Seq<int>, r: Seq<int>, shift: int, scale: int) -> bool {
    scale > 0 && r.len() == s.len() &&
    forall|i: int| 0 <= i < s.len() ==> r[i] == affine(s[i], shift, scale)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn rescale_to_unit(s: Seq<int>) -> (r: Seq<int>)
    requires s.len() >= 2,
             exists|i: int, j: int| (0 <= i < j < s.len()) && s[i] != s[j]
    ensures r.len() == s.len(),
            forall|i: int| 0 <= i < s.len() ==> 0 <= r[i] && r[i] <= 1,
            exists|i: int| 0 <= i < s.len() && r[i] == 0,
            exists|i: int| 0 <= i < s.len() && r[i] == 1,
            exists|shift: int, scale: int| scale > 0 && affine_seq(s, r, shift, scale)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}