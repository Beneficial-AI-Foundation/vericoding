use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
spec fn all_le_up_to_seq(seq: Seq<i32>, elem: i32, up_to: int) -> bool {
    forall|u: int| 0 <= u < up_to ==> seq[u] <= elem
}

spec fn all_gt_from_seq(seq: Seq<i32>, elem: i32, from: int) -> bool {
    forall|u: int| from < u < seq.len() ==> seq[u] > elem
}
// </vc-helpers>

// <vc-spec>
fn binary_search_rec(v: &Vec<i32>, elem: i32, c: usize, f: usize) -> (p: i32)
    requires
        sorted(v@),
        0 <= c <= f + 1 <= v.len(),//0<=c<=v.Length && -1<=f<v.Length && c<=f+1
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
    ensures
        -1 <= p < v.len(),
        (forall|u: int| 0 <= u <= p ==> v[u] <= elem) && (forall|w: int| p < w < v.len() ==> v[w] > elem),
    decreases f - c
// </vc-spec>
// <vc-code>
{
    if c > f {
        (#[verifier::truncate](c) as i32) - 1
    } else {
        let mid: usize = c + (f - c) / 2;
        let mid_int: int = mid as int;
        let v_seq: Seq<i32> = v@;
        if v_seq[mid_int] <= elem {
            assert(mid as int < v_seq.len());
            assert(forall|u: int| 0 <= u <= mid_int ==> #[trigger] v_seq[u] <= elem);
            assert(forall|w: int| f as int < w < v_seq.len() ==> #[trigger] v_seq[w] > elem);
            binary_search_rec(v, elem, mid + 1, f)
        } else {
            if mid == 0 {
                (#[verifier::truncate](c) as i32) - 1
            } else {
                assert(0 <= c as int <= mid_int <= v_seq.len());
                assert(forall|u: int| 0 <= u <= mid_int - 1 ==> #[trigger] v_seq[u] <= elem);
                assert(forall|w: int| mid_int <= w < v_seq.len() ==> #[trigger] v_seq[w] > elem);
                binary_search_rec(v, elem, c, mid - 1)
            }
        }
    }
}
// </vc-code>

fn main() {
}

}