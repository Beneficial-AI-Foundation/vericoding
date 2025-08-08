use vstd::prelude::*;

verus! {

fn add(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            #[trigger] a[i] + b[i] < 0x80000000int && a[i] + b[i] >= -0x80000000int,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i] + b[i],
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == a[j] + b[j],
            forall|j: int| 0 <= j < a.len() ==> 
                #[trigger] a[j] + b[j] < 0x80000000int && a[j] + b[j] >= -0x80000000int,
        decreases a.len() - i,
    {
        let sum = a[i] + b[i];
        res.push(sum);
        i = i + 1;
    }
    
    res
}

}

fn main() {}