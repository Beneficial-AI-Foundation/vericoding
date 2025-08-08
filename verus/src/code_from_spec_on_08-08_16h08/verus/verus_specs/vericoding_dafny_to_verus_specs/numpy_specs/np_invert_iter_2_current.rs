use vstd::prelude::*;

verus! {

// Helper function to define bitwise NOT operation (equivalent to Dafny's BitwiseNot)
spec fn bitwise_not(x: int) -> int {
    -x - 1
}

// Specification method equivalent to the Dafny version
fn invert(a: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() >= 0,
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == bitwise_not(a[i] as int),
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while idx < a.len()
        invariant
            result.len() == idx,
            forall|i: int| #![auto] 0 <= i < idx ==> result[i] == bitwise_not(a[i] as int),
        decreases a.len() - idx
    {
        let inverted_value = !a[idx];
        result.push(inverted_value);
        idx += 1;
    }
    
    result
}

fn main() {}

}