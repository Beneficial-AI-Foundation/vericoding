use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn array_product(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i64>) by (nonlinear_arith)
    requires
        a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| #![auto] 0 <= i && i < a.len() ==> result[i] == (a[i] as i64) * (b[i] as i64),
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| #![auto] 0 <= i && i < idx ==> result[i] == (a[i] as i64) * (b[i] as i64),
    {
        let product = (a[idx] as i64) * (b[idx] as i64);
        result.push(product);
        idx += 1;
    }
    
    result
}

fn main() {}
}