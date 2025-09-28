use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
proof fn sorted_monotone(v: &Vec<i32>, u: int, w: int)
    requires
        sorted(v@),
        0 <= u < w && w < v.len() as int,
    ensures
        v@[u] <= v@[w],
{
    assert(v@[u] <= v@[w]);
}

proof fn sorted_prefix_le(v: &Vec<i32>, elem: i32, c: int, m: int)
    requires
        sorted(v@),
        0 <= c <= m && m < v.len() as int,
        forall|k: int| 0 <= k < c ==> v@[k] <= elem,
        v@[m] <= elem,
    ensures
        forall|k: int| 0 <= k < m + 1 ==> v@[k] <= elem,
{
    assert(forall|k: int| 0 <= k < m + 1 ==>
        (if k < c {
            v@[k] <= elem
        } else {
            // For k in [c .. m]:
            // if k == m then v@[m] <= elem holds by precondition
            // else (k < m) monotonicity from sorted(v@) gives v@[k] <= v@[m]
            // so v@[k] <= v@[m] && v@[m] <= elem
            v@[k] <= v@[m] && v@[m] <= elem
        }));
    assert(forall|k: int| 0 <= k < m + 1 ==> v@[k] <= elem);
}

proof fn sorted_suffix_gt(v: &Vec<i32>, elem: i32, m: int)
    requires
        sorted(v@),
        m < v.len() as int,
        v@[m] > elem,
    ensures
        forall|k: int| m as int <= k < v.len() as int ==> v@[k] > elem,
{
    assert(forall|k: int| m as int <= k < v.len() as int ==> v@[k] > elem);
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
        // empty interval, return last index < c, i.e., c - 1
        (c as i32) - 1
    } else {
        let m: usize = (c + f) / 2;
        if v[m] <= elem {
            proof {
                // Show recursive-call preconditions for (m+1, f)
                assert(m + 1 <= f + 1);
                assert(f + 1 <= v.len());
                assert(m < v.len());
                assert((m as int) < v.len() as int);
                assert(0 <= m as int);
                // Bridge runtime index value to ghost view and show v@[m] <= elem
                assert(v@[m as int] == v[m as int]);
                assert(v@[m as int] <= elem);
                // show c <= m
                assert((c as int) <= (m as int));
                assert(0 <= c);
                // Now apply prefix lemma to get forall k < m+1: v@[k] <= elem
                sorted_prefix_le(v, elem, c as int, m as int);
            }
            binary_search_rec(v, elem, m + 1, f)
        } else {
            if m == 0 {
                // all indices >= 0 are > elem, so no index <= elem; return c-1
                (c as i32) - 1
            } else {
                proof {
                    // Show recursive-call preconditions for (c, m-1)
                    // 0 <= c <= (m-1) + 1 <= v.len()
                    assert(0 <= c);
                    assert(m >= 1);
                    assert(m - 1 + 1 <= v.len());
                    assert(m < v.len());
                    assert((m as int) < v.len() as int);
                    // Bridge runtime index value to ghost view and show v@[m] > elem
                    assert(v@[m as int] == v[m as int]);
                    assert(v@[m as int] > elem);
                    // Show suffix lemma precondition
                    sorted_suffix_gt(v, elem, m as int);
                }
                binary_search_rec(v, elem, c, m - 1)
            }
        }
    }
}
// </vc-code>

fn main() {
}

}