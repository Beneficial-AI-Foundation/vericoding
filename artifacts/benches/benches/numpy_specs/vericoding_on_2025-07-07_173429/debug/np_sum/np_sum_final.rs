use vstd::prelude::*;

verus! {

// ATOM - recursive function to compute sum of array elements
spec fn sum_array(a: Seq<i64>, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0
    } else {
        a[start] as int + sum_array(a, start + 1, end)
    }
}

// IMPL - iterative method to compute sum
fn sum(a: &[i64]) -> (res: i64)
    requires a.len() <= 10 && forall|i: int| 0 <= i < a.len() ==> -10 <= #[trigger] a@[i] <= 10
    ensures res as int == sum_array(a@, 0, a@.len() as int)
{
    let mut res = 0i64;
    let mut i = 0usize;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            res as int == sum_array(a@, 0, i as int),
            a.len() <= 10,
            forall|j: int| 0 <= j < a.len() ==> -10 <= #[trigger] a@[j] <= 10,
        decreases a.len() - i,
    {
        res = res + a[i];
        i = i + 1;
    }
    
    res
}

fn main() {}

}