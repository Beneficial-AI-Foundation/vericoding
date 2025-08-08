use vstd::prelude::*;

verus! {

// ATOM - recursive function to compute sum of array elements from start to end-1
spec fn sum_array(a: &[i32], start: int, end: int) -> int
    recommends 0 <= start <= end <= a.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        a[start] as int + sum_array(a, start + 1, end)
    }
}

// IMPL - iterative implementation with loop invariant  
#[verifier::external_body]
fn sum(a: &[i32]) -> (res: i32)
    ensures res as int == sum_array(a, 0, a.len() as int)
{
    let mut res = 0i32;
    let mut i = 0usize;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res as int == sum_array(a, 0, i as int)
        decreases a.len() - i
    {
        res = res + a[i];
        i = i + 1;
    }
    
    res
}

fn main() {}

}