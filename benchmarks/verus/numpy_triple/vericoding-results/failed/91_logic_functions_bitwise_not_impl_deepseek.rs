// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>


proof fn lemma_twos_complement_negation(a: i8)
    ensures
        (!a) as int == -(a as int + 1)
{
    /* helper modified by LLM (iteration 5): Remove proof block from spec function */
    let a_int: int = a as int;
    let not_a_int: int = !a as int;
    
    // Two's complement: !a = -a - 1
    assert(not_a_int == -(a_int + 1)) by(bit_vector);
}

// </vc-helpers>

// <vc-spec>
fn numpy_bitwise_not(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == -(x[i] as int + 1)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Same implementation as iteration 4 */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == -(x[j] as int + 1),
        decreases x.len() - i
    {
        let val = x[i];
        proof { lemma_twos_complement_negation(val); }
        result.push(!val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}