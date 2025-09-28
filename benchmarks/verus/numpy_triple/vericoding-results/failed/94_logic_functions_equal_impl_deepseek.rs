// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_vec_len<T>(v: Vec<T>)
    ensures
        (#[trigger] v@.len()) == v.len(),
{
    #[verifier::spec] let v_seq = v@;
    assert(v@.len() == v.len()) by {
        vstd::view::seq_axioms::lemma_seq_of_vec_len(v);
    };
}

spec fn elementwise_equality_spec<T>(x1: Seq<T>, x2: Seq<T>) -> Seq<bool> {
    Seq::new(x1.len(), |i: int| x1[i] == x2[i])
}
// </vc-helpers>

// <vc-spec>
fn numpy_equal<T>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires 
        x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed sequence module reference */
    proof {
        lemma_vec_len(x1);
        lemma_vec_len(x2);
    }
    let n = x1.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] == x2@[j]),
            forall|j: int| 0 <= j < i ==> (result@[j] == true || result@[j] == false),
            x1@ == x2@ ==> forall|j: int| 0 <= j < i ==> result@[j] == true,
    {
        let element_equal = x1[i] == x2[i];
        result.push(element_equal);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}