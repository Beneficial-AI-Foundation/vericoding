use vstd::prelude::*;

verus! {

fn cum_sum(a: &Vec<int>) -> (res: Vec<int>)
    ensures
        res.len() == a.len(),
        a.len() > 0 ==> res[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1] + a[i],
{
    let mut res: Vec<int> = Vec::new();
    
    for i in 0..a.len()
        invariant
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == if j == 0 { a[0] } else { res[j-1] + a[j] },
    {
        if i == 0 {
            res.push(a[i]);
        } else {
            /* code modified by LLM (iteration 1): Fixed borrowing issue by accessing previous element before mutable push */
            let prev_val = res[i-1];
            res.push(prev_val + a[i]);
        }
    }
    
    res
}

}

fn main() {}