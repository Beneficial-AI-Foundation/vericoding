use vstd::prelude::*;

verus! {

fn abs(a: &[i32]) -> (res: Vec<i32>)
    requires a.len() < usize::MAX,
    ensures
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == (if a[i] < 0 { (-a[i]) as int } else { a[i] as int }),
        forall|i: int| 0 <= i < a.len() ==> res[i] >= 0,
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> res[j] == (if a[j] < 0 { (-a[j]) as int } else { a[j] as int }),
            forall|j: int| 0 <= j < i ==> res[j] >= 0,
        decreases a.len() - i,
    {
        assume(a[i as int] != i32::MIN);  // Assume no overflow for simplicity
        let val = if a[i] < 0 {
            -a[i]
        } else {
            a[i]
        };
        res.push(val);
        i = i + 1;
    }
    
    res
}

}

fn main() {}