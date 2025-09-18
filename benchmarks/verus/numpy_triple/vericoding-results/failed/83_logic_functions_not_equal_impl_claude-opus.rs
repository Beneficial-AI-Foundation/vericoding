// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_not_equal<T: PartialEq>(x1: Vec<T>, x2: Vec<T>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i]),

        (x1@ == x2@) ==> (forall|i: int| 0 <= i < result.len() ==> result[i] == false),

        forall|i: int| 0 <= i < result.len() ==> result[i] == (x2[i] != x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed assertion by using proper indexing */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] != x2[j]),
            forall|j: int| 0 <= j < i ==> result[j] == (x2[j] != x1[j]),
        decreases x1.len() - i,
    {
        let not_equal = x1[i] != x2[i];
        result.push(not_equal);
        
        proof {
            assert(result.len() == i + 1);
            assert(result[(result.len() - 1) as int] == not_equal);
            assert((x1[i as int] != x2[i as int]) == (x2[i as int] != x1[i as int]));
            assert(forall|j: int| 0 <= j < i ==> result[j] == (x1[j] != x2[j]));
            assert(result[i as int] == not_equal);
            assert(forall|j: int| 0 <= j <= i ==> result[j] == (x1[j] != x2[j]));
            assert(forall|j: int| 0 <= j <= i ==> result[j] == (x2[j] != x1[j]));
        }
        
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}