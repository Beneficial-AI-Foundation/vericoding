use vstd::prelude::*;

verus! {

fn multiply(a: &Vec<i32>, b: &Vec<i32>) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i] * b@[i] <= 2147483647,
        forall|i: int| 0 <= i < a.len() ==> #[trigger] a@[i] * b@[i] >= -2147483648
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res@[i] == a@[i] * b@[i]
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> result@[j] == a@[j] * b@[j]
    {
        result.push(a[i] * b[i]);
        i += 1;
    }
    
    result
}

fn main() {
    let a = vec![1, 2, 3, 4];
    let b = vec![2, 3, 4, 5];
    let result = multiply(&a, &b);
    /* code modified by LLM (iteration 1): removed println! as it's not supported in Verus verification */
    // println!("Result: {:?}", result);
}

}