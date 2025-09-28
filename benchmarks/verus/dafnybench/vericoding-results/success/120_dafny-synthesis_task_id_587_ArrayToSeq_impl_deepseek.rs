use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn array_to_seq_spec(a: &[i32]) -> Seq<i32>
    decreases a.len()
{
    Seq::new(a.len() as nat, |i: int| a[i])
}

proof fn array_to_seq_lemma(a: &[i32], i: int)
    requires
        0 <= i < a.len(),
    ensures
        array_to_seq_spec(a)[i] == a[i],
{
    reveal(array_to_seq_spec);
}
// </vc-helpers>

// <vc-spec>
fn array_to_seq(a: &[i32]) -> (s: Vec<i32>)
    ensures
        s.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> s[i] == a[i],
// </vc-spec>
// <vc-code>
{
    let mut s = Vec::new();
    let mut idx: usize = 0;
    while idx < a.len()
        invariant
            idx <= a.len(),
            s.len() == idx,
            forall|j: int| 0 <= j < idx ==> s@[j] == a[j],
        decreases a.len() - idx,
    {
        s.push(a[idx]);
        proof {
            array_to_seq_lemma(a, idx as int);
        }
        idx = idx + 1;
    }
    s
}
// </vc-code>

fn main() {
}

}