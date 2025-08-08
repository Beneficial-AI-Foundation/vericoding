use vstd::prelude::*;

verus! {

spec fn bitwise_not(x: int) -> int {
    -x - 1
}

fn bitwise_not_exec(x: i32) -> (result: i32)
    requires x > i32::MIN,
    ensures result as int == bitwise_not(x as int)
{
    -x - 1
}

fn invert(a: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() >= 0,
        forall|i: int| 0 <= i < a.len() ==> a[i] > i32::MIN,
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] as int == bitwise_not(a[i] as int),
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] as int == bitwise_not(a[j] as int),
            forall|k: int| 0 <= k < a.len() ==> a[k] > i32::MIN,
        decreases a.len() - i,
    {
        assert(a[i as int] > i32::MIN);
        res.push(bitwise_not_exec(a[i]));
        i = i + 1;
    }
    
    res
}

}