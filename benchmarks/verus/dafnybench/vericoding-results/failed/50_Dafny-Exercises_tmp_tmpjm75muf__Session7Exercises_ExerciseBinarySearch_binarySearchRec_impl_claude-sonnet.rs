use vstd::prelude::*;

verus! {

spec fn sorted(s: Seq<i32>) -> bool {
    forall|u: int, w: int| 0 <= u < w < s.len() ==> s[u] <= s[w]
}







//Recursive binary search

// <vc-helpers>
spec fn in_bounds(i: int, len: int) -> bool {
    0 <= i < len
}

proof fn lemma_binary_search_bounds(c: usize, f: usize, mid: usize)
    requires c <= f, mid == c + (f - c) / 2
    ensures c <= mid <= f
{
}

proof fn lemma_progress(c: usize, f: usize, mid: usize)
    requires c <= f, mid == c + (f - c) / 2
    ensures c < f ==> (mid < f || c < mid)
{
}

proof fn lemma_cast_bounds(f: usize, v_len: int)
    requires f + 1 <= v_len, v_len <= usize::MAX
    ensures -1 <= f as i32 < v_len
{
}

proof fn lemma_mid_minus_one_valid(c: usize, f: usize, mid: usize)
    requires c <= f, mid == c + (f - c) / 2, c < f
    ensures mid >= 1
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
        proof {
            lemma_cast_bounds(f, v.len() as int);
        }
        return (f as i32);
    }
    
    let mid = c + (f - c) / 2;
    
    proof {
        lemma_binary_search_bounds(c, f, mid);
        lemma_progress(c, f, mid);
    }
    
    if v[mid] <= elem {
        let recursive_result = binary_search_rec(v, elem, mid + 1, f);
        proof {
            assert(forall|k: int| 0 <= k < mid + 1 ==> v[k] <= elem);
            assert(forall|k: int| f < k < v.len() ==> v[k] > elem);
        }
        recursive_result
    } else {
        proof {
            lemma_mid_minus_one_valid(c, f, mid);
        }
        let recursive_result = binary_search_rec(v, elem, c, mid - 1);
        proof {
            assert(forall|k: int| 0 <= k < c ==> v[k] <= elem);
            assert(forall|k: int| (mid - 1) < k < v.len() ==> v[k] > elem);
        }
        recursive_result
    }
}
// </vc-code>

fn main() {
}

}