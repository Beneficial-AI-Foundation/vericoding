// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added PartialEq trait bound to fix compilation error */
fn lemma_vec_indexing<T: PartialEq>(v1: Vec<T>, v2: Vec<T>, i: int)
    requires
        v1.len() == v2.len(),
        0 <= i < v1.len(),
    ensures
        (v1[i] == v2[i]) == true || (v1[i] == v2[i]) == false,
{
}

fn lemma_equal_seqs_imply_equal_elements<T: PartialEq>(s1: Seq<T>, s2: Seq<T>, i: int)
    requires
        s1 == s2,
        0 <= i < s1.len(),
    ensures
        s1[i] == s2[i],
{
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
    /* code modified by LLM (iteration 5): fixed compilation by adding PartialEq trait bound */
    let mut result: Vec<bool> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < x1.len()
        invariant
            idx <= x1.len(),
            result.len() == idx,
            x1.len() == x2.len(),
            forall|i: int| 0 <= i < idx ==> result[i] == (x1[i as int] == x2[i as int]),
            forall|i: int| 0 <= i < idx ==> (result[i] == true || result[i] == false),
        decreases x1.len() - idx
    {
        let equal_val = x1[idx] == x2[idx];
        result.push(equal_val);
        idx = idx + 1;
    }
    
    proof {
        if x1@ == x2@ {
            assert forall|i: int| 0 <= i < result.len() implies result[i] == true by {
                lemma_equal_seqs_imply_equal_elements(x1@, x2@, i);
            }
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}