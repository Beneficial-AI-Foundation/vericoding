// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn ones_seq(n: nat) -> Seq<i32> { Seq::new(n, |i: int| 1) }

proof fn lemma_ones_seq_index(n: nat, i: int)
    requires
        0 <= i < n,
    ensures
        ones_seq(n)[i] == 1
{ }
// </vc-helpers>

// <vc-spec>
fn ones_like<T>(a: &Vec<T>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1,
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    while result.len() < a.len()
        invariant
            result.len() <= a.len(),
            forall|j: int| 0 <= j < result.len() ==> result@[j] == 1,
        decreases a.len() - result.len()
    {
        result.push(1);
    }
    result
}
// </vc-code>

}
fn main() {}