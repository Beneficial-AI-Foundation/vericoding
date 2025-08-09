use vstd::prelude::*;

verus! {

fn cum_sum(a: &Vec<int>) -> (res: Vec<int>)
    ensures
        res.len() == a.len(),
        a.len() > 0 ==> res[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> res[i] == res[i-1] + a[i],
{
    let mut res = Vec::new();
    
    if a.len() == 0 {
        return res;
    }
    
    res.push(a[0]);
    
    let mut i = 1;
    /* code modified by LLM (iteration 1): added decreases clause to fix compilation error */
    while i < a.len()
        invariant
            res.len() == i,
            i <= a.len(),
            i > 0 ==> res[0] == a[0],
            forall|j: int| 1 <= j < i ==> res[j] == res[j-1] + a[j],
        decreases a.len() - i
    {
        let sum = res[i-1] + a[i];
        res.push(sum);
        i += 1;
    }
    
    res
}

}

fn main() {}