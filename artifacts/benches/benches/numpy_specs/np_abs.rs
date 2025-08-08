use vstd::prelude::*;

verus! {

fn abs(a: &Vec<i32>) -> (res: Vec<i32>)
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == (if a[i] < 0 { -a[i] as int } else { a[i] as int }),
        forall|i: int| 0 <= i < a.len() ==> res[i] >= 0,
{
    let mut result: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == (if a[i] < 0 { -a[i] as int } else { a[i] as int }),
            forall|i: int| 0 <= i < idx ==> result[i] >= 0,
        decreases a.len() - idx,
    {
        proof {
            assume(a[idx as int] > i32::MIN); // For overflow safety
        }
        let val = if a[idx] < 0 { -a[idx] } else { a[idx] };
        result.push(val);
        idx += 1;
    }
    
    result
}

}