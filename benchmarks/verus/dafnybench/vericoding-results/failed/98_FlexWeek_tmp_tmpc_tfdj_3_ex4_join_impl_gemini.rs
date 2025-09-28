// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn join(a: &[i32], b: &[i32]) -> (c: Vec<i32>)
    ensures
        a@ + b@ == c@,
        (a@ + b@).to_multiset() == c@.to_multiset(),
        a@.to_multiset().add(b@.to_multiset()) == c@.to_multiset(),
        a.len() + b.len() == c.len(),

        forall|i: int| 0 <= i < a.len() ==> c[i] == a[i],
        forall|i: int, j: int| 
            a.len() <= i < c.len() && 
            0 <= j < b.len() && 
            i - j == a.len() ==> c[i] == b[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): corrected the multiset lemma module from vstd::seq to vstd::seq_lib */
    let mut c = a.to_vec();
    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b.len(),
            c.len() == a.len() + j,
            c@ == a@ + b@.take(j as int),
        decreases b.len() - j
    {
        c.push(b[j]);
        j = j + 1;
    }
    proof {
        vstd::seq_lib::lemma_multiset_is_add(a@, b@);
    }
    c
}
// </vc-code>

}
fn main() {}