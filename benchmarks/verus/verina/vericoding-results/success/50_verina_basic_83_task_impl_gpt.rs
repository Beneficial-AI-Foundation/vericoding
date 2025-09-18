// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple min helper, not used by main code but available for proofs/examples */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
/* helper modified by LLM (iteration 2): predicate for index validity */
spec fn is_valid_index(i: int, len: int) -> bool { 0 <= i && i < len }
/* helper modified by LLM (iteration 2): trivial arithmetic lemma */
proof fn add_zero_lemma(x: int) ensures x + 0 == x { }
// </vc-helpers>

// <vc-spec>
fn concat(a: &Vec<i32>, b: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len() + b.len(),
        forall|k: int| 0 <= k < a.len() ==> result[k] == a[k],
        forall|k: int| 0 <= k < b.len() ==> result[k + a.len()] == b[k],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): add decreases clauses and strengthen invariants for termination */
    let mut r: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i as int,
            i <= a.len(),
            r.len() == i,
            forall|k: int| 0 <= k < i as int ==> r[k] == a[k],
        decreases (a.len() - i) as int
    {
        r.push(a[i]);
        i += 1;
    }
    let alen: usize = a.len();
    let mut j: usize = 0;
    while j < b.len()
        invariant
            0 <= j as int,
            j <= b.len(),
            r.len() == alen + j,
            forall|k: int| 0 <= k < alen as int ==> r[k] == a[k],
            forall|k: int| 0 <= k < j as int ==> r[k + alen as int] == b[k],
        decreases (b.len() - j) as int
    {
        r.push(b[j]);
        j += 1;
    }
    r
}
// </vc-code>

}
fn main() {}