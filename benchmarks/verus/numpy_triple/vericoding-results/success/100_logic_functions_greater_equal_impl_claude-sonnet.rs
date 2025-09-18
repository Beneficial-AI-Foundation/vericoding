// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed to accept int instead of i32 */
spec fn element_ge(a: int, b: int) -> bool { a >= b }

proof fn ge_reflexive(a: int)
    ensures element_ge(a, a)
{
}

proof fn ge_antisymmetric(a: int, b: int)
    requires element_ge(a, b) && element_ge(b, a)
    ensures a == b
{
}
// </vc-helpers>

// <vc-spec>
fn numpy_greater_equal(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> (result[i] <==> x1@[i] >= x2@[i]),

        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,

        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] == true && x2@[i] >= x1@[i]) ==> x1@[i] == x2@[i],

        forall|i: int| 0 <= i < result.len() ==> (result[i] == true || result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking and precondition issues */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> (result@[j] <==> x1@[j] >= x2@[j]),
        decreases x1.len() - i
    {
        assert(i < x1.len());
        assert(i < x2.len());
        let comparison = x1[i] >= x2[i];
        result.push(comparison);
        
        proof {
            if comparison {
                ge_reflexive(x1@[i as int] as int);
                if i < x2.len() && x2@[i as int] >= x1@[i as int] {
                    ge_antisymmetric(x1@[i as int] as int, x2@[i as int] as int);
                }
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}