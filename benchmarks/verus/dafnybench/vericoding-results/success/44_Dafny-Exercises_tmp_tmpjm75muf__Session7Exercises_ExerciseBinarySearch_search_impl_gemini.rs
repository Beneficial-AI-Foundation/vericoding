// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<int>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}

fn binary_search(v: &[int], elem: int) -> (p: i32)
    requires sorted(v@)
    ensures 
        -1 <= p < v@.len() &&
        (forall|u: int| 0 <= u <= p ==> v@[u] <= elem) &&
        (forall|w: int| p < w < v@.len() ==> v@[w] > elem)
{
    assume(false);
    -1
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [fully implemented the proof] */
proof fn lemma_binary_search_correctness(v: Seq<int>, elem: int, p: int)
    requires
        sorted(v),
        -1 <= p < v.len(),
        (forall|u: int| 0 <= u <= p ==> v[u] <= elem),
        (forall|w: int| p < w < v.len() ==> v[w] > elem),
    ensures
        v.contains(elem) <==> (p >= 0 && v[p] == elem),
{
    if v.contains(elem) {
        let k = choose |k: int| 0 <= k < v.len() && v[k] == elem;
        if p < k {
            assert(v[k] > elem);
            assert(false);
        }
        assert(k <= p);
        assert(p >= 0);
        assert(v[p] <= elem);
        if k < p {
            assert(sorted(v));
            assert(v[k] <= v[p]);
        }
        assert(elem <= v[p]);
        assert(v[p] == elem);
        assert(p >= 0 && v[p] == elem);
    }
    if p >= 0 && v[p] == elem {
        assert(v.contains(elem));
    }
}
// </vc-helpers>

// <vc-spec>
fn search(v: &[int], elem: int) -> (b: bool)
    requires sorted(v@)
    ensures b == v@.contains(elem)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [call lemma in proof block and use if-expression for safe indexing] */
    let p = binary_search(v, elem);
    proof {
        lemma_binary_search_correctness(v@, elem, p as int);
    }
    if p >= 0 {
        v[p as usize] == elem
    } else {
        false
    }
}
// </vc-code>

}
fn main() {}