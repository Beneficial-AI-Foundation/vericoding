// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): provide sequence update helper and pointwise lemma for replaced element */
spec fn replace_at(s: Seq<i32>, j: int, v: i32) -> Seq<i32> { s.update(j, v) }
/* helper modified by LLM (iteration 3): lemma ensures properties of replace_at at and away from index */
proof fn lemma_replace_pointwise(s: Seq<i32>, j: int, v: i32)
    requires 0 <= j < s.len()
    ensures
        replace_at(s, j, v).len() == s.len(),
        replace_at(s, j, v)[j] == v,
        forall|k: int| 0 <= k < s.len() && k != j ==> replace_at(s, j, v)[k] == s[k]
{ }
// </vc-helpers>

// <vc-spec>
fn test_array_elements(a: &Vec<i32>, j: usize) -> (result: Vec<i32>)
    requires j < a.len(),
    ensures
        result.len() == a.len(),
        result[j as int] == 60,
        forall|k: int| 0 <= k < a.len() && k != j ==> result[k] == a[k],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): strengthen loop invariants and add bounds assertions before indexing */
    let n = a.len();
    let mut r: Vec<i32> = Vec::new();
    for i in 0..n
        invariant
            r.len() == i,
            i <= n,
            n == a.len(),
            forall|k: int| 0 <= k < i as int ==> r[k] == if k == j as int { 60 } else { a@[k] },
    {
        if i == j {
            r.push(60);
        } else {
            assert(i < n);
            assert(n == a.len());
            assert(i < a.len());
            let v = a[i];
            r.push(v);
        }
    }
    assert(r.len() == n);
    assert(n == a.len());
    proof {
        assert(r.len() == a.len());
        assert(forall|k: int| 0 <= k < a.len() ==> r[k] == if k == j as int { 60 } else { a@[k] });
    }
    r
}
// </vc-code>

}
fn main() {}