use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
// </vc-spec>
// <vc-code>
{
    if sequences.len() == 0 {
        // Empty sequence trivially satisfies the condition
        return true;
    }
    
    let first_len = sequences[0].len();
    let mut i: usize = 1;
    
    while i < sequences.len()
        invariant
            0 <= i <= sequences.len(),
            forall |j: int| 0 <= j < i as int ==> #[trigger] sequences[j].len() == first_len,
            first_len == sequences[0].len(),
    {
        if sequences[i].len() != first_len {
            assert(sequences[i as int].len() != sequences[0].len());
            return false;
        }
        i = i + 1;
    }
    
    assert(forall |j: int| 0 <= j < sequences.len() ==> #[trigger] sequences[j].len() == first_len);
    assert(forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> 
        sequences[i].len() == first_len && sequences[j].len() == first_len);
    assert(forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> 
        sequences[i].len() == sequences[j].len());
    
    true
}
// </vc-code>

fn main() {
}

}