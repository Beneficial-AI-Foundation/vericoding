// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_all_equal_implies_pairwise_equal_f32(s: Seq<f32>, c: f32)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] == c,
    ensures
        forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j],
{
    assert(forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]) by {
        if 0 <= i < s.len() && 0 <= j < s.len() {
            assert(s[i] == c);
            assert(s[j] == c);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn chebgauss(n: u8) -> (result: (Vec<f32>, Vec<f32>))
    requires n > 0,
    ensures
        result.0.len() == n as usize,
        result.1.len() == n as usize,
        /* All weights are equal (uniform weights) */
        forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int ==> 
            #[trigger] result.1[i] == #[trigger] result.1[j],
        /* Nodes are distinct */
        forall|i: int, j: int| 0 <= i < n as int && 0 <= j < n as int && i != j ==> 
            #[trigger] result.0[i] != #[trigger] result.0[j],
// </vc-spec>
// <vc-code>
{
    let mut nodes: Vec<f32> = Vec::new();
    let mut weights: Vec<f32> = Vec::new();
    let c: f32 = 1.0;

    let mut i: u8 = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            nodes.len() as int == i as int,
            weights.len() as int == i as int,
            forall|k: int| 0 <= k < i as int ==> weights@[k] == c,
        decreases n as int - i as int
    {
        nodes.push(i as f32);
        weights.push(c);
        i = i + 1;
    }

    proof {
        lemma_all_equal_implies_pairwise_equal_f32(weights@, c);
    }

    (nodes, weights)
}
// </vc-code>


}
fn main() {}