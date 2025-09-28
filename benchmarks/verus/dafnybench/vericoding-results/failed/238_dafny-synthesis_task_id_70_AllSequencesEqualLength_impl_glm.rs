use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
// </vc-spec>
// <vc-code>
{
    if sequences.len() == 0 {
        return true;
    }
    let n = sequences@[0].len();
    let mut i = 1;
    while i < sequences.len()
        invariant 1 <= i <= sequences.len()
        invariant {
            forall|k: int| 0 <= k < i ==> sequences@[k].len() == n
        }
    {
        if sequences@[i].len() != n {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

fn main() {
}

}