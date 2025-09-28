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
    let first_len: int = sequences[0].len();
    let mut result: bool = true;
    let mut i: int = 1;
    while i < sequences.len()
        invariant
            1 <= i <= sequences.len(),
            result <==> (forall |k: int| 0 <= k < i ==> sequences[k].len() == first_len),
            sequences[0].len() == first_len,
    {
        result = result && (sequences[i].len() == first_len);
        i = i + 1;
    }
    assert(result <==> (forall |k: int| 0 <= k < sequences.len() ==> sequences[k].len() == first_len));
    result
}
// </vc-code>

fn main() {
}

}