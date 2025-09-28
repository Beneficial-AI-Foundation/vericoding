// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_greater_equal(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> (result[i] <==> x1@[i] as int >= x2@[i] as int),

        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,

        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true && x2@[i] as int >= x1@[i] as int) ==> x1@[i] as int == x2@[i] as int,

        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to the while loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (result@[j] <==> x1@[j] as int >= x2@[j] as int),
        decreases x1.len() - i
    {
        let ge = x1[i] >= x2[i];
        result.push(ge);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}