use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
spec fn mid(a: usize, b: usize) -> usize {
    (a + b) / 2
}

proof fn lemma_mid_range(a: usize, b: usize)
    requires
        a <= b,
    ensures
        a <= mid(a, b) <= b,
{
}

proof fn lemma_mid_decreases(a: usize, b: usize)
    requires
        a < b,
    ensures
        mid(a, b) - a < b - a,
        b - mid(a, b) < b - a,
{
    reveal(mid);
    assert((b - a) > 0);
}

proof fn lemma_sorted_transitive(s: Seq<i32>, i: int, j: int, k: int)
    requires
        sorted(s),
        0 <= i <= j <= k < s.len(),
    ensures
        s[i] <= s[k],
{
}

proof fn lemma_sorted_implies_leq(s: Seq<i32>, i: int, j: int)
    requires
        sorted(s),
        0 <= i <= j < s.len(),
    ensures
        s[i] <= s[j],
{
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
        -1
    } else {
        let m = (c + f) / 2;
        proof { lemma_mid_range(c, f); }
        if v[m] <= elem {
            if m == f {
                m as i32
            } else {
                proof {
                    assert(forall|k: int| f < k < v@.len() ==> v@[k] > elem);
                    assert(forall|k: int| 0 <= k < c ==> v@[k] <= elem);
                    assert(sorted(v@));
                }
                proof { lemma_mid_decreases(c, f); }
                let (p) = binary_search_rec(v, elem, m + 1, f);
                proof {
                    assert(0 <= m + 1 <= f + 1 <= v@.len());
                    assert(forall|k: int| 0 <= k < m + 1 ==> v@[k] <= elem) by {
                        assert(0 <= k < m + 1 ==> k < m + 1);
                        if (k < m + 1) {
                            if (k < m) {
                                lemma_sorted_implies_leq(v@, k, m);
                                assert(v@[k] <= v@[m]);
                                assert(v@[m] <= elem);
                            } else if (k == m) {
                                assert(v@[m] <= elem);
                            }
                        }
                    }
                    assert(forall|k: int| f < k < v@.len() ==> v@[k] > elem);
                    assert((f as int) - (m as int + 1) < (f as int) - (c as int));
                }
                p
            }
        } else {
            proof {
                assert(forall|k: int| f < k < v.len() ==> v@[k] > elem);
                assert(forall|k: int| 0 <= k < c ==> v@[k] <= elem);
                assert(sorted(v@));
            }
            proof { lemma_mid_decreases(c, f); }
            let (p) = binary_search_rec(v, elem, c, m - 1);
            proof {
                assert(0 <= c <= (m - 1) + 1 <= v@.len());
                assert(forall|k: int| 0 <= k < c ==> v@[k] <= elem);
                assert(forall|k: int| m - 1 < k < v@.len() ==> v@[k] > elem) by {
                    assert(m - 1 < k < v@.len() ==> v@[k] > elem);
                    if (m - 1 < k < v@.len()) {
                        assert(v@[m] > elem);
                        if (k <= m) {
                            lemma_sorted_implies_leq(v@, k, m);
                            assert(v@[k] <= v@[m]);
                        } else {
                            assert(v@[k] > elem);
                        }
                    }
                }
                assert(((m - 1) as int) - (c as int) < (f as int) - (c as int));
            }
            p
        }
    }
}
// </vc-code>

fn main() {
}

}