use vstd::prelude::*;

verus! {

fn sign(a: &[i32]) -> (res: Vec<i32>)
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (a[i] > 0 ==> res[i] == 1)
            &&& (a[i] == 0 ==> res[i] == 0)
            &&& (a[i] < 0 ==> res[i] == -1)
        }
{
    let mut res = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            res.len() == idx,
            forall|i: int| 0 <= i < idx ==> {
                &&& (a[i] > 0 ==> res[i] == 1)
                &&& (a[i] == 0 ==> res[i] == 0)
                &&& (a[i] < 0 ==> res[i] == -1)
            }
        decreases a.len() - idx
    {
        let sign_val = if a[idx] > 0 {
            1
        } else if a[idx] == 0 {
            0
        } else {
            -1
        };
        
        res.push(sign_val);
        idx += 1;
    }
    
    res
}

}

fn main() {}