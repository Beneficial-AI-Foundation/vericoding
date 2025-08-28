use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    if sequences.len() == 0nat {
        return true;
    }
    
    let first_len = sequences@[0].len();
    
    for i in 0..sequences.len() as usize
        invariant
            forall |k: int| 0 <= k < i ==> sequences@[k].len() == first_len
    {
        if sequences@[i].len() != first_len {
            return false;
        }
    }
    
    true
}
// </vc-code>

fn main() {
}

}