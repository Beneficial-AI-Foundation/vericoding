use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
    requires
        0< i <= v.len(),
    ensures
        v.take(i as int).drop_last() == v.take(i-1),
{
    assert(v.take(i as int).drop_last()=~=v.take(i-1));
}

proof fn lemma_seq_take_all<T>(v: Seq<T>)
    ensures
        v == v.take(v.len() as int),
{
    assert(v =~= v.take(v.len() as int));
}

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
            y@ == x@.take(i as int).filter(|k:u64| k%3 == 0),
        decreases x.len() - i,
    {
        /* code modified by LLM (iteration 1): use usize indexing for executable code instead of int casting */
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        /* code modified by LLM (iteration 1): added proof annotations to maintain loop invariant with proper casting */
        proof {
            assert(x@.take((i + 1) as int) == x@.take(i as int).push(x[i as int]));
            if x[i] % 3 == 0 {
                assert(x@.take((i + 1) as int).filter(|k:u64| k%3 == 0) == 
                       x@.take(i as int).filter(|k:u64| k%3 == 0).push(x[i as int]));
            } else {
                assert(x@.take((i + 1) as int).filter(|k:u64| k%3 == 0) == 
                       x@.take(i as int).filter(|k:u64| k%3 == 0));
            }
        }
        i += 1;
    }
    /* code modified by LLM (iteration 1): added proof to establish postcondition from loop invariant */
    proof {
        lemma_seq_take_all(x@);
        assert(x@.take(i as int) == x@);
        assert(y@ == x@.filter(|k:u64| k%3 == 0));
    }
}
}