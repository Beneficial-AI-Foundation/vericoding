// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn all_non_zero_prefix(v: Seq<i32>, n: int) -> bool {
    forall|j: int| 0 <= j < n ==> v@[j] != 0
}
// </vc-helpers>

// <vc-spec>
fn mfirst_cero(v: &[i32]) -> (i: usize)
    ensures
        i <= v.len(),
        forall|j: int| 0 <= j < i as int ==> v@[j] != 0,
        i != v.len() ==> v@[i as int] == 0,
{
    assume(false);
    0
}
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            all_non_zero_prefix(v.view(), i as int),
        decreases v.len() - i
    {
        if v[i] == 0 {
            return i;
        }
        i = i + 1;
    }
    i
}
// </vc-code>

}
fn main() {}