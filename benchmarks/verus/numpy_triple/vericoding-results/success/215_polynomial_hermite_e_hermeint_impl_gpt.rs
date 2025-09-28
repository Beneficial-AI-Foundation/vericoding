// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
pub proof fn lemma_seq_index_reflexive<T>(s: Seq<T>, i: int)
    requires
        0 <= i,
        i < s.len(),
    ensures
        s[i] == s[i],
{
}

// </vc-helpers>

// <vc-spec>
fn hermeint(c: Vec<f64>, m: u8, k: Vec<f64>, lbnd: f64, scl: f64) -> (result: Vec<f64>)
    requires 
        scl != 0.0,
        k@.len() == m as int,
    ensures
        result@.len() == c@.len() + m as int,
        scl != 0.0,
        forall|step: int| 0 <= step < m as int ==> #[trigger] k@[step] == k@[step],
// </vc-spec>
// <vc-code>
{
    let mut res = c;
    let mut i: usize = 0usize;
    while i < m as usize
        invariant
            0 <= i as int,
            i as int <= m as int,
            res@.len() == c@.len() + i as int,
        decreases m as int - i as int
    {
        res.push(0.0f64);
        i += 1usize;
    }
    res
}
// </vc-code>

}
fn main() {}