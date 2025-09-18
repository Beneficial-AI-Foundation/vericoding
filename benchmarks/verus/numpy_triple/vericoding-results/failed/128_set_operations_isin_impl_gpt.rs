// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): boolean contrapositive lemma to derive p ==> b from !b ==> !p */
proof fn contrapositive_bool(b: bool, p: bool)
    ensures
        (!b ==> !p) ==> (p ==> b)
{ }

/* helper modified by LLM (iteration 3): predicate for membership in a Vec */
spec fn isin(x: f32, v: Vec<f32>) -> bool { exists|j: int| 0 <= j < v.len() && x == v[j] }

/* helper modified by LLM (iteration 3): lemma that universal inequality implies non-existence */
proof fn not_exists_from_all_neq(x: f32, v: Vec<f32>)
    ensures
        (forall|j: int| 0 <= j < v.len() ==> x != v[j]) ==> !(exists|j: int| 0 <= j < v.len() && x == v[j])
{ }
// </vc-helpers>

// <vc-spec>
fn numpy_isin(element: Vec<f32>, test_elements: Vec<f32>) -> (result: Vec<bool>)
    ensures 
        result.len() == element.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true <==> exists|j: int| 0 <= j < test_elements.len() && element[i] == test_elements[j])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): implement isin via nested loops; fix loop invariant syntax and use int indices */
    let n = element.len();
    let m = test_elements.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant 0 <= i <= n
        invariant res.len() == i
        invariant forall|k: int| 0 <= k < res.len() ==> (res[k] == true <==> exists|j: int| 0 <= j < m && element[k] == test_elements[j])
        decreases n - i
    {
        let x = element[i];
        let mut found: bool = false;
        let mut j: int = 0;
        while j < m
            invariant 0 <= j <= m
            invariant found ==> exists|jj: int| 0 <= jj < j && x == test_elements[jj]
            invariant !found ==> forall|jj: int| 0 <= jj < j ==> x != test_elements[jj]
            decreases m - j
        {
            if x == test_elements[j] {
                found = true;
            }
            j = j + 1;
        }
        proof {
            assert(j == m);
            assert(found ==> exists|jj: int| 0 <= jj < m && x == test_elements[jj]);
            assert(!found ==> forall|jj: int| 0 <= jj < m ==> x != test_elements[jj]);
            not_exists_from_all_neq(x, test_elements);
            assert(!found ==> !(exists|jj: int| 0 <= jj < m && x == test_elements[jj]));
            contrapositive_bool(found, exists|jj: int| 0 <= jj < m && x == test_elements[jj]);
            assert((exists|jj: int| 0 <= jj < m && x == test_elements[jj]) ==> found);
        }
        let old_len = res.len();
        res.push(found);
        proof {
            assert(old_len == i);
            assert(res[old_len] == found);
            assert(element[old_len] == x);
            assert(found ==> exists|jj: int| 0 <= jj < m && element[old_len] == test_elements[jj]);
            assert((exists|jj: int| 0 <= jj < m && element[old_len] == test_elements[jj]) ==> found);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}