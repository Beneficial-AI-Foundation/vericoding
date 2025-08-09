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
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> result[j] == bitwise_not(a[j] as int),
    {
        let inverted = !a[i];
        result.push(inverted);
    }
    
    result
}

fn main() {}

}