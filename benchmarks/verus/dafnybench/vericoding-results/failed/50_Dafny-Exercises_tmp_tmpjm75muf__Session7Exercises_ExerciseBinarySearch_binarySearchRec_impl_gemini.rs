// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn binary_search_rec(v: &Vec<i32>, elem: i32, c: usize, f: usize) -> (p: i32)
    requires
        sorted(v@),
        0 <= c <= f + 1 <= v.len(),
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
    ensures
        -1 <= p < v.len(),
        (forall|u: int| 0 <= u <= p ==> v[u] <= elem) && (forall|w: int| p < w < v.len() ==> v[w] > elem),
    decreases f - c
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed `forall` proof block syntax */
    if c > f {
        return f as i32;
    }

    let m = c + (f - c) / 2;

    if v[m] <= elem {
        binary_search_rec(v, elem, m + 1, f)
    } else {
        if m == 0 {
            assert forall|w: int| 0 <= w < v@.len() implies v@[w] > elem by {
                if w > 0 {
                    assert(v@[w] >= v@[0]);
                }
            };
            -1
        } else {
            binary_search_rec(v, elem, c, m - 1)
        }
    }
}
// </vc-code>

}
fn main() {}