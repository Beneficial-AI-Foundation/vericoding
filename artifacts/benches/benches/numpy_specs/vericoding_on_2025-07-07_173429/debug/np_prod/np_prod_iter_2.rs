use vstd::prelude::*;

verus! {

spec fn prod_array(a: &[i32], start: int, end: int) -> int
    recommends 0 <= start <= end <= a.len()
    decreases end - start
{
    if start >= end {
        1
    } else {
        a[start] as int * prod_array(a, start + 1, end)
    }
}

fn prod(a: &[i32]) -> (res: i32)
    ensures res as int == prod_array(a, 0, a.len() as int)
{
    let mut res: i32 = 1;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res as int == prod_array(a, 0, i as int),
        decreases a.len() - i
    {
        res = res * a[i];
        i = i + 1;
    }
    
    res
}

fn main() {}

}