use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
// no helpers needed
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
    if c == f + 1 {
        let p: i32 = c as i32 - 1;
        proof {
            assert(-1 <= p);
            assert(c <= v.len());
            assert(p < v.len() as i32);

            assert(forall|u: int| 0 <= u <= p as int ==> v@[u] <= elem) by {
                assert forall|u: int| 0 <= u <= p as int ==> v@[u] <= elem {
                    if 0 <= u <= p as int {
                        assert(p as int == c as int - 1);
                        assert(0 <= u < c as int);
                        assert(v@[u] <= elem);
                    }
                }
            };

            assert(forall|w: int| p as int < w < v.len() as int ==> v@[w] > elem) by {
                assert forall|w: int| p as int < w < v.len() as int ==> v@[w] > elem {
                    if p as int < w < v.len() as int {
                        assert(p as int == c as int - 1);
                        assert(f as int == p as int);
                        assert(f as int < w);
                        assert(v@[w] > elem);
                    }
                }
            };
        }
        p
    } else {
        let m: usize = c + (f - c) / 2;
        proof {
            assert(c <= m);
            assert(m <= f);
// </vc-code>

fn main() {
}

}