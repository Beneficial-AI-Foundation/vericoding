use vstd::prelude::*;

verus! {

fn subtract(a: &Vec<i32>, b: &Vec<i32>) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i] as int) - (b[i] as int) >= i32::MIN &&
            (a[i] as int) - (b[i] as int) <= i32::MAX,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] res[i] == a[i] - b[i],
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] res[j] == a[j] - b[j],
            forall|k: int| 0 <= k < a.len() ==> 
                (a[k] as int) - (b[k] as int) >= i32::MIN &&
                (a[k] as int) - (b[k] as int) <= i32::MAX,
        decreases a.len() - i,
    {
        let val = a[i] - b[i];
        res.push(val);
        i = i + 1;
    }
    
    res
}

}

fn main() {}