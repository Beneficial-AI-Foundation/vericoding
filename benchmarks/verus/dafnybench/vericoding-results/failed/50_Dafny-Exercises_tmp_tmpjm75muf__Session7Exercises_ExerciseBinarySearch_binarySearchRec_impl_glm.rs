use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
proof fn lemma_binary_search_bounds(v: &Vec<i32>, elem: i32, c: usize, f: usize, m: usize)
    requires
        sorted(v@),
        0 <= c <= f + 1 <= v.len(),
        forall|k: int| 0 <= k < c ==> v@[k] <= elem,
        forall|k: int| f < k < v.len() ==> v@[k] > elem,
        c <= m <= f,
    ensures
        v@[m] <= elem ==> {
            forall|k: int| 0 <= k <= m ==> v@[k] <= elem
        },
        v@[m] > elem ==> {
            forall|k: int| m < k < v.len() ==> v@[k] > elem
        }
{
    if v@[m] <= elem {
        assert forall|k: int| 0 <= k <= m implies v@[k] <= elem by {
            if k < c {
                assert(v@[k] <= elem) by {
                    reveal(sorted);
                }
            } else {
                assert(c <= k <= m && m <= f);
                assert(c <= k <= f);
                assert(v@[k] <= v@[m] <= elem) by {
                    reveal(sorted);
                }
            }
        }
    } else {
        assert forall|k: int| m < k < v.len() implies v@[k] > elem by {
            if k > f {
                assert(v@[k] > elem) by {
                    reveal(sorted);
                }
            } else {
                assert(m < k <= f && c <= m);
                assert(m < k <= f);
                assert(v@[k] >= v@[m] > elem) by {
                    reveal(sorted);
                }
            }
        }
    }
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
        return (f as i32);
    }
    let m = (c + f) / 2;
    proof { 
        lemma_binary_search_bounds(v, elem, c, f, m);
    }
    if v[m] <= elem {
        let res = binary_search_rec(v, elem, m + 1, f);
        proof {
            assert forall|u: int| 0 <= u <= res implies v@[u] <= elem by {
                if u <= m {
                    assert(v@[u] <= elem) by {
                        lemma_binary_search_bounds(v, elem, c, f, m);
                    }
                } else {
                    assert(v@[u] <= elem) by {
                        assert(m + 1 <= u <= res && res <= f);
                    }
                }
            }
            assert forall|w: int| res < w < v.len() implies v@[w] > elem by {
                assert(res < w < v.len());
                assert(m + 1 <= res + 1 <= w < v.len());
            }
        }
        return res;
    } else {
        let res = binary_search_rec(v, elem, c, m - 1);
        proof {
            assert forall|u: int| 0 <= u <= res implies v@[u] <= elem by {
                assert(0 <= u <= res && res <= m - 1);
                assert(0 <= u <= m - 1 < m <= f);
            }
            assert forall|w: int| res < w < v.len() implies v@[w] > elem by {
                if w <= m {
                    assert(res < w <= m && m <= f);
                    assert(v@[w] > elem) by {
                        lemma_binary_search_bounds(v, elem, c, f, m);
                    }
                } else {
                    assert(w > m && m < w < v.len());
                    assert(v@[w] > elem) by {
                        lemma_binary_search_bounds(v, elem, c, f, m);
                    }
                }
            }
        }
        return res;
    }
}
// </vc-code>

fn main() {
}

}