use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier(external_body)]
#[verifier(opaque)]
fn poly_contains_int<T>(s: Seq<T>, val: T) -> bool {
    unimplemented!()
}
// </vc-helpers>

// <vc-spec>
fn any_value_exists(seq1: Seq<int>, seq2: Seq<int>) -> (result: bool)
    ensures result <==> (exists|i: int| 0 <= i < seq1.len() && seq2.contains(seq1[i]))
// </vc-spec>
// <vc-code>
{
    let mut i: nat = 0;
    while i < seq1.len()
        invariant
            0 <= i,
            i <= seq1.len(),
            forall|j: int| 0 <= j && (j as nat) < i ==> !seq2.contains(seq1.index(j as nat)),
    {
        if seq2.contains(seq1.index(i)) {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {}

}