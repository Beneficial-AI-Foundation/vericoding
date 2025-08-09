use vstd::prelude::*;

verus! {

fn cum_sum(a: &Vec<int>) -> (res: Vec<int>)
    ensures
        res.len() == a.len(),
        a.len() > 0 ==> res[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1] + a[i],
{
    /* code modified by LLM (iteration 1): Added explicit type annotation to fix compilation error */
    let mut res: Vec<int> = Vec::new();
    
    for i in 0..a.len()
        invariant
            res.len() == i,
            /* code modified by LLM (iteration 1): Fixed loop invariant to properly specify cumulative sum property */
            forall|j: int| 0 <= j < i ==> res[j] == if j == 0 { a[0] } else { res[j-1] + a[j] },
    {
        if i == 0 {
            res.push(a[i]);
        } else {
            res.push(res[i-1] + a[i]);
        }
    }
    
    res
}

}

fn main() {}