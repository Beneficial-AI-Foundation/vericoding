// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_sequences_equal_length(sequences: Seq<Seq<int>>) -> (result: bool)
    ensures result <==> (forall |i: int, j: int| 0 <= i < sequences.len() && 0 <= j < sequences.len() ==> sequences[i].len() == sequences[j].len())
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): wrapped logic in a proof block to fix ghost context error and used nat for loop counter. */
{
    proof {
        if sequences.len() <= 1 {
            return true;
        }

        let first_len = sequences[0].len();
        let mut i: nat = 1;
        while i < sequences.len()
            invariant
                1 <= i && i <= sequences.len(),
                forall|k: nat| k < i ==> sequences[k as int].len() == first_len,
            decreases sequences.len() - i
        {
            if sequences[i as int].len() != first_len {
                return false;
            }
            i = i + 1;
        }
        return true;
    }
}
// </vc-code>

}
fn main() {}