// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add bounds checking and sequence lemma for verification */
fn equal_lemma(x1: Vec<String>, x2: Vec<String>) -> (v: Vec<bool>)
    requires 
        x1.len() == x2.len(),
    ensures
        v.len() == x1.len(),
        forall|i: int| 0 <= i < v.len() ==> v[i] == (x1[i] == x2[i]),
{
    let mut result: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    assert(x1.len() == x2.len());
    while j < x1.len()
        invariant
            0 <= j <= x1.len(),
            result.len() == j,
            forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] == x2[i]),
            x1.len() == x2.len(),
        decreases x1.len() - j,
    {
        assert(j < x1.len());
        assert(j < x2.len());
        let eq = x1[j] == x2[j];
        result.push(eq);
        j = j + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i as int] == (x1[i as int] == x2[i as int]),
        forall|i: int| 0 <= i < result.len() ==> (result[i as int] == true <==> x1[i as int] == x2[i as int]),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i as int] == true,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Add bounds checking and proper indexing verification */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> result[j] == (x1[j] == x2[j]),
            x1.len() == x2.len(),
        decreases x1.len() - i,
    {
        assert(i < x1.len());
        assert(i < x2.len());
        let eq = x1[i] == x2[i];
        result.push(eq);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}