use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_seq_contains(s1: Seq<int>, s2: Seq<int>, i: int)
    requires
        0 <= i < s1.len(),
        s2.contains(s1[i]),
    ensures
        exists|k: int| 0 <= k < s1.len() && s2.contains(s1[k])
{
    assert(s2.contains(s1[i]));
}

proof fn lemma_seq_contains_not(s1: Seq<int>, s2: Seq<int>)
    requires
        forall|j: int| 0 <= j < s1.len() ==> !s2.contains(s1[j]),
    ensures
        !exists|i: int| 0 <= i < s1.len() && s2.contains(s1[i])
{
    assert(forall|j: int| 0 <= j < s1.len() ==> !s2.contains(s1[j]));
}
// </vc-helpers>

// <vc-spec>
fn any_value_exists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < seq1.len() && seq2.contains(seq1[i]))
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let n = seq1.len() as int;
    while i < n
        invariant
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> !seq2.contains(seq1[j])
    {
        if seq2.contains(seq1[i]) {
            proof {
                lemma_seq_contains(seq1, seq2, i);
            }
            return true;
        }
        i = i + 1;
    }
    proof {
        lemma_seq_contains_not(seq1, seq2);
    }
    false
}
// </vc-code>

fn main() {}

}