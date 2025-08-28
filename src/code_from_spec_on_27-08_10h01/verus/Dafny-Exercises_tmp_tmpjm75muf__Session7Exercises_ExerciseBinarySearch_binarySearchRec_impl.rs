use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
spec fn valid_range(c: usize, f: usize, len: usize) -> bool {
    c <= len && f < len && c <= f + 1
}

spec fn partition_property(v: Seq<i32>, elem: i32, p: int) -> bool {
    (forall|u: int| 0 <= u <= p ==> v[u] <= elem) && 
    (forall|w: int| p < w < v.len() ==> v[w] > elem)
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    if c > f {
        #[verifier::truncate]
        (f as i32)
    } else {
        let mid = c + (f - c) / 2;
        if v[mid] <= elem {
            binary_search_rec(v, elem, mid + 1, f)
        } else {
            if mid == 0 {
                -1
            } else {
                binary_search_rec(v, elem, c, mid - 1)
            }
        }
    }
}
// </vc-code>

fn main() {
}

}