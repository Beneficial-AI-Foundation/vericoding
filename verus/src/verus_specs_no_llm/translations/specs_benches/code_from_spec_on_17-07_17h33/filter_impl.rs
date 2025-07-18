use vstd::prelude::*;
fn main() {}

verus!{

/* code modified by LLM (iteration 2): added helper lemma to prove filter property extension */
proof fn lemma_filter_extend<T>(s: Seq<T>, pred: spec_fn(T) -> bool, i: int, elem: T)
    requires 
        0 <= i < s.len(),
    ensures 
        s.subrange(0, i + 1).filter(pred) == s.subrange(0, i).filter(pred).push(elem) <==> pred(elem) && s[i] == elem,
        s.subrange(0, i + 1).filter(pred) == s.subrange(0, i).filter(pred) <==> !pred(elem) || s[i] != elem,
{
    assert(s.subrange(0, i + 1) == s.subrange(0, i).push(s[i]));
}

//IMPL myfun4
pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
        decreases x.len() - i
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
            /* code modified by LLM (iteration 2): added proof step for case when element is added */
            proof {
                lemma_filter_extend(x@, |k:u64| k%3 == 0, i as int, x[i]);
                assert(x@.subrange(0, i as int + 1).filter(|k:u64| k%3 == 0) == 
                       x@.subrange(0, i as int).filter(|k:u64| k%3 == 0).push(x[i]));
            }
        } else {
            /* code modified by LLM (iteration 2): added proof step for case when element is not added */
            proof {
                lemma_filter_extend(x@, |k:u64| k%3 == 0, i as int, x[i]);
                assert(x@.subrange(0, i as int + 1).filter(|k:u64| k%3 == 0) == 
                       x@.subrange(0, i as int).filter(|k:u64| k%3 == 0));
            }
        }
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): added assertion to help prove postcondition from loop invariant */
    assert(i == x.len());
    assert(x@.subrange(0, i as int) == x@);
}
}