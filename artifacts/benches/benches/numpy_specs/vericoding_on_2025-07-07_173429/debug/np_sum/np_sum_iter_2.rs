use vstd::prelude::*;

verus! {

// ATOM
spec fn sum_array(a: &[i32], start: int, end: int) -> int
    recommends 0 <= start <= end <= a.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        a[start] + sum_array(a, start + 1, end)
    }
}

// IMPL
fn sum(a: &[i32]) -> (res: i32)
    ensures res == sum_array(a, 0, a.len() as int)
{
    let mut res = 0i32;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res == sum_array(a, 0, i as int),
        decreases a.len() - i
    {
        // Added assertions to help Verus prove the loop invariant by showing how sum_array expands
        assert(sum_array(a, 0, (i + 1) as int) == a[i as int] + sum_array(a, (i + 1) as int, (i + 1) as int));
        assert(sum_array(a, (i + 1) as int, (i + 1) as int) == 0);
        assert(sum_array(a, 0, (i + 1) as int) == a[i as int] + sum_array(a, 0, i as int));
        
        res = res + a[i];
        i = i + 1;
    }
    
    res
}

fn main() {}

}