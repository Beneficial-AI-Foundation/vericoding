use vstd::prelude::*;
fn main() {}

verus!{
//IMPL myfun4
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    let mut i = 0;
    /* code modified by LLM (iteration 4): fixed loop invariant to properly track filtered elements */
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
        decreases x.len() - i,
    {
        /* code modified by LLM (iteration 4): added assertion to help verification with correct indexing */
        assert(x@.subrange(0, (i+1) as int) == x@.subrange(0, i as int).push(x[i as int]));
        
        if x[i] % 3 == 0 {
            y.push(x[i]);
            /* code modified by LLM (iteration 4): added assertion to maintain invariant when element is divisible by 3 with correct indexing */
            assert(y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0).push(x[i as int]));
            assert(x@.subrange(0, (i+1) as int).filter(|k:u64| k%3 == 0) == 
                   x@.subrange(0, i as int).filter(|k:u64| k%3 == 0).push(x[i as int]));
        } else {
            /* code modified by LLM (iteration 4): added assertion to maintain invariant when element is not divisible by 3 */
            assert(x@.subrange(0, (i+1) as int).filter(|k:u64| k%3 == 0) == 
                   x@.subrange(0, i as int).filter(|k:u64| k%3 == 0));
        }
        i += 1;
    }
    /* code modified by LLM (iteration 4): added final assertion to prove postcondition */
    assert(i == x.len());
    assert(x@.subrange(0, i as int) == x@);
}
}