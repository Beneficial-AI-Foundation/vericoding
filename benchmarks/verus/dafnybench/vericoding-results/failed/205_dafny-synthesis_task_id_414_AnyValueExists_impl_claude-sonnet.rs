use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn any_value_exists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < seq1.len() && seq2.contains(seq1[i]))
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    while i < seq1.len()
        invariant
            0 <= i <= seq1.len(),
            forall|j: int| 0 <= j < i ==> !seq2.contains(seq1[j])
    {
        if seq2.contains(seq1[i as int]) {
            assert(0 <= i < seq1.len() && seq2.contains(seq1[i as int]));
            return true;
        }
        i = i + 1;
    }
    assert(forall|j: int| 0 <= j < seq1.len() ==> !seq2.contains(seq1[j]));
    false
}
// </vc-code>

fn main() {}

}