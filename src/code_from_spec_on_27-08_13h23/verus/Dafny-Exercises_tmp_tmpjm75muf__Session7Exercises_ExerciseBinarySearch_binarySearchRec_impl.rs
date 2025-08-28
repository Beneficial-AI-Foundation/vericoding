use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
proof fn lemma_middle_element(v: Seq<i32>, elem: i32, c: int, f: int, mid: int)
    requires
        sorted(v),
        0 <= c <= f + 1 <= v.len(),
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
        c <= mid <= f,
    ensures
        mid < v.len() ==> (v[mid] <= elem ==> (forall|u: int| 0 <= u <= mid ==> v[u] <= elem)),
        mid < v.len() ==> (v[mid] > elem ==> (forall|w: int| mid < w < v.len() ==> v[w] > elem)),
{
    if mid < v.len() {
        if v[mid] <= elem {
            assert forall|u: int| 0 <= u <= mid implies v[u] <= elem by {
                if u < c {
                    assert(v[u] <= elem);
                } else if u == mid {
                    assert(v[u] <= elem);
                } else {
                    assert(c <= u < mid);
                    assert(v[u] <= v[mid]);
                    assert(v[mid] <= elem);
                    assert(v[u] <= elem);
                }
            }
        } else {
            assert forall|w: int| mid < w < v.len() implies v[w] > elem by {
                if w <= f {
                    assert(v[mid] <= v[w]);
                    assert(v[mid] > elem);
                    assert(v[w] > elem);
                } else {
                    assert(v[w] > elem);
                }
            }
        }
    }
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
{
    if c > f {
        return (c as i32) - 1;
    }

    let mid = (c + f) / 2;
    let mid_i32 = mid as i32;

    if v[mid] == elem {
        return mid_i32;
    } else if v[mid] < elem {
        proof {
            lemma_middle_element(v@, elem, c as int, f as int, mid as int);
        }
        binary_search_rec(v, elem, mid + 1, f)
    } else {
        proof {
            lemma_middle_element(v@, elem, c as int, f as int, mid as int);
        }
        binary_search_rec(v, elem, c, mid - 1)
    }
}
// </vc-code>

fn main() {
}

}