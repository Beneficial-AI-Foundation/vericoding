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
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res@[j] == a@[j] * b@[j],
            a.len() == b.len(),
            forall|k: int| 0 <= k < a.len() ==> a@[k] * b@[k] <= 2147483647,
            forall|k: int| 0 <= k < a.len() ==> a@[k] * b@[k] >= -2147483648
        decreases a.len() - i
    {
        proof {
            assert(i < a.len());
            assert(i < b.len()) by {
                assert(a.len() == b.len());
            }
            assert(a@[i as int] * b@[i as int] <= 2147483647);
            assert(a@[i as int] * b@[i as int] >= -2147483648);
        }
        let val_a = a[i];
        let val_b = b[i];
        res.push(val_a * val_b);
        i += 1;
    }
    
    res
}

fn main() {
}

}