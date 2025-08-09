use vstd::prelude::*;

verus! {

fn cum_prod(a: &[i32]) -> (res: Vec<i32>)
    ensures
        res.len() == a.len(),
        res.len() > 0 ==> res[0int] == a[0int],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1] * a[i],
{
    let mut res = Vec::new();
    
    if a.len() == 0 {
        return res;
    }
    
    res.push(a[0]);
    
    let mut idx = 1;
    /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
    while idx < a.len()
        invariant
            res.len() == idx,
            idx <= a.len(),
            res.len() > 0 ==> res[0int] == a[0int],
            forall|i: int| 1 <= i < idx ==> res[i] == res[i-1] * a[i],
        decreases a.len() - idx
    {
        let prod = res[idx - 1] * a[idx];
        res.push(prod);
        idx += 1;
    }
    
    res
}

/* code modified by LLM (iteration 1): Removed println! macro usage and replaced with exec-only function */
fn print_vec(v: &Vec<i32>) {
    // Print function stubbed out - println! is not supported in Verus
}

fn main() {
    let arr = [2, 3, 4];
    let result = cum_prod(&arr);
    print_vec(&result);
}

}