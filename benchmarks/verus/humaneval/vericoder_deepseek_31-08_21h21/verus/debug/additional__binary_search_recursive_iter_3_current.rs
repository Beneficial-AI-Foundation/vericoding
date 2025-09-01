use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_sorted_sublist(v: &[i32], start: int, end: int)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= start <= end <= v.len()
    ensures
        forall|i: int, j: int| start <= i < j < end ==> v[i] <= v[j]
{
}

proof fn lemma_sorted_transitive(v: &[i32], a: int, b: int, c: int)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= a <= b <= c < v.len()
    ensures
        v[a] <= v[c]
{
}

proof fn lemma_sorted_prefix(v: &[i32], elem: i32, bound: int)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= bound <= v.len(),
        forall|k: int| 0 <= k < bound ==> v[k] <= elem
    ensures
        forall|k: int| 0 <= k < bound ==> v[k] <= elem
{
}

proof fn lemma_sorted_suffix(v: &[i32], elem: i32, bound: int)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= bound <= v.len(),
        forall|k: int| bound < k < v.len() ==> v[k] > elem
    ensures
        forall|k: int| bound < k < v.len() ==> v[k] > elem
{
}

proof fn lemma_interval_monotonic(v: &[i32], elem: i32, c1: int, f1: int, c2: int, f2: int)
    requires
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= c1 <= c2 <= f2 <= f1 <= v.len(),
        forall|k: int| 0 <= k < c1 ==> v[k] <= elem,
        forall|k: int| f1 < k < v.len() ==> v[k] > elem
    ensures
        forall|k: int| 0 <= k < c2 ==> v[k] <= elem,
        forall|k: int| f2 < k < v.len() ==> v[k] > elem
{
    if c2 > c1 {
        assert forall|k: int| 0 <= k < c2 implies v[k] <= elem by {
            if k < c1 {
                assert(v[k] <= elem);
            } else {
                assert(c1 <= k < c2);
                assert(v[c1] <= v[k]);
                assert(v[k] <= elem);
            }
        };
    }
    
    if f2 < f1 {
        assert forall|k: int| f2 < k < v.len() implies v[k] > elem by {
            if k > f1 {
                assert(v[k] > elem);
            } else {
                assert(f2 < k <= f1);
                assert(v[k] <= v[f1]);
                assert(v[f1] <= elem);
                assert(v[k] > elem);
            }
        };
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_search_recursive(v: &[i32], elem: i32, c: isize, f: isize) -> (p: isize)
    // pre-conditions-start
    requires
        v.len() <= 100_000,
        forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] <= v[j],
        0 <= c <= f + 1 <= v.len(),
        forall|k: int| 0 <= k < c ==> v[k] <= elem,
        forall|k: int| f < k < v.len() ==> v[k] > elem,
    // pre-conditions-end
    // post-conditions-start
    ensures
        -1 <= p < v.len(),
        forall|u: int| 0 <= u <= p ==> v[u] <= elem,
        forall|w: int| p < w < v.len() ==> v[w] > elem,
    // post-conditions-end
    decreases f - c + 1
// </vc-spec>
// <vc-code>
{
    if c > f {
        proof {
            lemma_sorted_prefix(v, elem, c as int);
            lemma_sorted_suffix(v, elem, f as int);
        }
        return c - 1;
    }
    
    let m = c + (f - c) / 2;
    
    proof {
        lemma_interval_monotonic(v, elem, c as int, f as int, c as int, m as int);
        lemma_interval_monotonic(v, elem, c as int, f as int, (m + 1) as int, f as int);
    }
    
    let vm = v[m as usize];
    
    if vm <= elem {
        binary_search_recursive(v, elem, m + 1, f)
    } else {
        binary_search_recursive(v, elem, c, m - 1)
    }
}
// </vc-code>

fn main() {}
}