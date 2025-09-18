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
/* code modified by LLM (iteration 5): Fixed the assertion for Vec::push to explicitly state the length relation before and after the push operation. */
{
    let mut result: Vec<bool> = Vec::new();
    result.reserve(x1.len());

    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] != x2@[j]),
            
        decreases x1.len() - i,
    {
        let prior_len = i;
        result.push(x1.int_index(i) != x2.int_index(i));
        i = i + 1;
        proof {
            assert(result.len() == prior_len + 1);
        }
    }
    result
}
// </vc-code>

}
fn main() {}