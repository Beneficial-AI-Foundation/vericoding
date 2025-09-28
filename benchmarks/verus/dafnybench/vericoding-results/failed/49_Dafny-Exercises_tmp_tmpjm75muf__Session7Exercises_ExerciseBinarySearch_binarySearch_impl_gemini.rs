// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to relate sorted property of mapped sequence back to original sequence */
proof fn sorted_map_values_lemma(s: Seq<i32>, i: int, j: int)
    requires
        sorted(s.map_values(|v: i32| v as int)),
        0 <= i < j < s.len(),
    ensures
        (s[i] as int) <= (s[j] as int),
{
}
// </vc-helpers>

// <vc-spec>
fn binary_search(v: &Vec<i32>, elem: i32) -> (p: i32)
    requires sorted(v@.map_values(|val: i32| val as int)),
    ensures ({
        &&& -1 <= p < v.len()
        &&& forall|u: int| 0 <= u <= p ==> v@[u] <= elem as int
        &&& forall|w: int| p < w < v.len() ==> v@[w] > elem as int
    }),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added assertions utilizing a helper lemma to guide the SMT prover in maintaining loop invariants */
{
    let mut low: usize = 0;
    let mut high: usize = v.len();

    while low < high
        invariant
            low <= high <= v.len(),
            forall|i: int| 0 <= i < low as int ==> v@[i] <= elem,
            forall|i: int| high as int <= i < v.len() as int ==> v@[i] > elem,
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        if v[mid] > elem {
            let old_high = high;
            assert forall|i: int| mid as int <= i < old_high as int implies v@[i] > elem by {
                if (mid as int) < i {
                    sorted_map_values_lemma(v@, mid as int, i);
                }
            };
            high = mid;
        } else { // v[mid] <= elem
            assert forall|i: int| low as int <= i <= mid as int implies v@[i] <= elem by {
                if i < (mid as int) {
                    sorted_map_values_lemma(v@, i, mid as int);
                }
            };
            low = mid + 1;
        }
    }

    return (low as i32) - 1;
}
// </vc-code>

}
fn main() {}