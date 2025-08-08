use vstd::prelude::*;

verus! {

fn sign(a: &Vec<i32>) -> (res: Vec<i32>)
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& (a[i] > 0 ==> res[i] == 1)
            &&& (a[i] == 0 ==> res[i] == 0)
            &&& (a[i] < 0 ==> res[i] == -1)
        }
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> {
                &&& (a[j] > 0 ==> res[j] == 1)
                &&& (a[j] == 0 ==> res[j] == 0)
                &&& (a[j] < 0 ==> res[j] == -1)
            }
        decreases a.len() - i
    {
        if a[i] > 0 {
            res.push(1);
        } else if a[i] == 0 {
            res.push(0);
        } else {
            res.push(-1);
        }
        i = i + 1;
    }
    
    res
}

}

fn main() {}