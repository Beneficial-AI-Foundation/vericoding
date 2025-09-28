use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_contains_index<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.contains(s[i]),
{
}

proof fn lemma_not_exists<A>(s: Seq<A>, f: spec_fn(int, A) -> bool)
    requires
        forall|i: int, a: A| 0 <= i < s.len() ==> !f(i, s[i]),
    ensures
        !(exists|i: int| 0 <= i < s.len() && f(i, s[i])),
{
}

spec fn contains_pred(a: int) -> spec_fn(int, int) -> bool {
    |j: int, b: int| b == a
}

proof fn lemma_forall_implies_not_exists<A>(s: Seq<A>, f: spec_fn(int, A) -> bool)
    requires
        forall|i: int, a: A| 0 <= i < s.len() && a == s[i] ==> !f(i, a),
    ensures
        !(exists|i: int| 0 <= i < s.len() && f(i, s[i])),
{
    lemma_not_exists(s, f);
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn any_value_exists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < seq1.len() && seq2.contains(seq1[i]))
// </vc-spec>
// <vc-code>
{
    let mut found = false;
    let mut idx: int = 0;
    while idx < seq1.len()
        invariant
            0 <= idx <= seq1.len(),
            forall|j: int| 0 <= j < idx ==> !seq2.contains(seq1[j]),
            found == (exists|i: int| 0 <= i < idx && seq2.contains(seq1[i])),
    {
        if seq2.contains(seq1[idx as int]) {
            found = true;
        }
        idx = idx + 1;
    }
    proof {
        if !found {
            lemma_forall_implies_not_exists(seq1, |i: int, a: int| seq2.contains(a));
        }
    }
    found
}
// </vc-code>
// </vc-code>

fn main() {}

}