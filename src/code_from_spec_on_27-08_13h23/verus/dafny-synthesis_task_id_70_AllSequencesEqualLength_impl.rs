use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers in this case
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
// </vc-spec>
// </vc-spec>

// <vc-code>
fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
{
    if sequences.len() == 0 {
        return true;
    }
    
    let first_len = sequences[0].len();
    let mut i: usize = 0;
    
    while i < sequences.len()
        invariant
            0 <= i <= sequences.len(),
            forall |k: int| 0 <= k < i ==> sequences[k].len() == first_len
    {
        if sequences[i].len() != first_len {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {
}

}