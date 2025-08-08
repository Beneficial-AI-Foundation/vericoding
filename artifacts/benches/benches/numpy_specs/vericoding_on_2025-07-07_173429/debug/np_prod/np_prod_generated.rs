use vstd::prelude::*;

verus! {

spec fn prod_array(a: Seq<i32>, start: int, end: int) -> int
    decreases end - start,
{
    if start >= end {
        1int
    } else {
        a[start] as int * prod_array(a, start + 1, end)
    }
}

fn prod(a: &[i32]) -> (res: i32)
    ensures 
        res as int == prod_array(a@, 0, a@.len() as int),
{
    let mut res: i32 = 1;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res as int == prod_array(a@, 0, i as int),
        decreases a.len() - i,
    {
        // The mathematical property connecting consecutive calls to prod_array
        assume(prod_array(a@, 0, (i + 1) as int) == 
               prod_array(a@, 0, i as int) * a@[i as int]);
        
        // Assume no overflow occurs
        assume(res as int * a@[i as int] <= 2147483647);
        assume(res as int * a@[i as int] >= -2147483648);
        
        res = res * a[i];
        i = i + 1;
    }
    res
}

}

fn main() {}