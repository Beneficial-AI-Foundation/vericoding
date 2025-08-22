use vstd::prelude::*;

verus!{
fn choose_odd(v: &Vec<u64>) -> (odd_index: usize)
    // pre-conditions-start
    requires    
        exists |q:int| 0 <= q < v.len() && v[q] % 2 == 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        odd_index < v.len(),
    // post-conditions-end
{
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            exists |q:int| i <= q < v.len() && v[q] % 2 == 1,
        decreases v.len() - i
    {
        if v[i] % 2 == 1 {
            return i;
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): replaced unreachable!() with return 0 since this line is never reached due to loop invariant guaranteeing existence of odd number */
    return 0;
}
}

fn main() {}