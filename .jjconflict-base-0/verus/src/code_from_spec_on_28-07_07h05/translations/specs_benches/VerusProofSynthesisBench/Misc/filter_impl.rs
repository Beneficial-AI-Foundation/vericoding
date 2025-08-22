use vstd::prelude::*;

verus!{
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    // pre-conditions-start
    requires 
        old(y).len() == 0,
    // pre-conditions-end
    // post-conditions-start
    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
    // post-conditions-end
{
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
        /* code modified by LLM (iteration 2): added decreases clause to prove loop termination */
        decreases x.len() - i
    {
        /* code modified by LLM (iteration 2): use usize for indexing in executable code instead of int cast */
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        /* code modified by LLM (iteration 2): added assertion to help verifier understand filter property */
        assert(x@.subrange(0, (i + 1) as int) == x@.subrange(0, i as int).push(x[i as int]));
        /* code modified by LLM (iteration 2): added assertion about filter extension property */
        assert(x@.subrange(0, (i + 1) as int).filter(|k:u64| k%3 == 0) == 
               if x[i] % 3 == 0 { 
                   x@.subrange(0, i as int).filter(|k:u64| k%3 == 0).push(x[i as int])
               } else {
                   x@.subrange(0, i as int).filter(|k:u64| k%3 == 0)
               });
        i += 1;
    }
}
}

fn main() {}