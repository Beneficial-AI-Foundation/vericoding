use vstd::prelude::*;

verus! {

// ATOM
spec fn sum_array(a: Seq<i32>, start: int, end: int) -> int
    recommends 0 <= start <= end <= a.len()
    decreases end - start when 0 <= start < end
{
    if start == end { 
        0 
    } else { 
        a[start] as int + sum_array(a, start + 1, end) 
    }
}

// SPEC
fn sum(a: &Vec<i32>) -> (res: i32)
    ensures res as int == sum_array(a@, 0, a@.len() as int)
{
    let mut total: i32 = 0;
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while i < a.len()
        invariant 
            i <= a.len(),
            total as int == sum_array(a@, 0, i as int)
        decreases a.len() - i
    {
        total = total + a[i];
        i = i + 1;
    }
    
    total
}

}

fn main() {}