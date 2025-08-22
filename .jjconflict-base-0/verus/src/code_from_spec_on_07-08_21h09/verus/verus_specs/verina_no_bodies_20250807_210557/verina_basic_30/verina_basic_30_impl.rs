use vstd::prelude::*;

verus! {

// Precondition for elementWiseModulo  
spec fn elementWiseModulo_precond(a: Seq<i32>, b: Seq<i32>) -> bool {
    a.len() == b.len() && a.len() > 0 &&
    forall|i: int| 0 <= i < b.len() ==> b[i] != 0
}

// Main function that performs element-wise modulo
fn elementWiseModulo(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        a.len() > 0,
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove termination */
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == a[j] % b[j],
        decreases a.len() - i
    {
        result.push(a[i] % b[i]);
        i += 1;
    }
    
    result
}

// Postcondition specification  
spec fn elementWiseModulo_postcond(a: Seq<i32>, b: Seq<i32>, result: Seq<i32>) -> bool {
    result.len() == a.len() &&
    forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i]
}

} // verus!

fn main() {
    let a = vec![10, 21, 8, 15];
    let b = vec![3, 4, 5, 7];
    let result = elementWiseModulo(a, b);
    println!("Result: {:?}", result);
}