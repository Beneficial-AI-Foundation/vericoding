use vstd::prelude::*;

verus! {

fn cum_prod(a: &[i32]) -> (res: Vec<i32>)
    ensures
        res.len() == a.len(),
        res.len() > 0 ==> res[0int] == a[0int],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1] * a[i],
{
    let mut res = Vec::new();
    
    for i in 0..a.len()
        invariant
            res.len() == i,
            i > 0 ==> res[0int] == a[0int],
            forall|j: int| 1 <= j < i ==> res[j] == res[j-1] * a[j],
    {
        if i == 0 {
            res.push(a[i]);
        } else {
            let prev = res[i-1];
            res.push(prev * a[i]);
        }
    }
    
    res
}

fn main() {
    let arr = [1, 2, 3, 4];
    let result = cum_prod(&arr);
    println!("{:?}", result);
}

}