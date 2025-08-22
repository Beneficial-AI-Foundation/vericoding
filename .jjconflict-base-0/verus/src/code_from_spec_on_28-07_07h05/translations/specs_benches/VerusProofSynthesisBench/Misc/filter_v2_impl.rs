use vstd::prelude::*;

verus!{
proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
    // pre-conditions-start
    requires
        0 < i <= v.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        v.take(i as int).drop_last() == v.take(i-1),
    // post-conditions-end
{
    // impl-start
    assert(v.take(i as int).drop_last() =~= v.take(i-1));
    // impl-end
}
// pure-end

proof fn lemma_seq_take_all<T>(v: Seq<T>)
    // post-conditions-start
    ensures
        v == v.take(v.len() as int),
    // post-conditions-end
{
    // impl-start
    assert(v =~= v.take(v.len() as int));
    // impl-end
}
// pure-end

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
            i <= x.len(),
            y@ == x@.take(i as int).filter(|k:u64| k%3 == 0),
        decreases x.len() - i
    {
        /* code modified by LLM (iteration 2): added assertion to help prove loop invariant maintenance */
        assert(x@.take((i + 1) as int) == x@.take(i as int).push(x@[i as int]));
        
        if x[i] % 3 == 0 {
            /* code modified by LLM (iteration 2): store previous state of y@ before modification */
            let ghost prev_y = y@;
            y.push(x[i]);
            /* code modified by LLM (iteration 2): added assertion to prove invariant when element is added */
            assert(y@ == prev_y.push(x@[i as int]));
            assert(x@.take(i as int).filter(|k:u64| k%3 == 0).push(x@[i as int]) == 
                   x@.take((i + 1) as int).filter(|k:u64| k%3 == 0));
        } else {
            /* code modified by LLM (iteration 2): added assertion to prove invariant when element is not added */
            assert(x@[i as int] % 3 != 0);
            assert(x@.take(i as int).filter(|k:u64| k%3 == 0) == 
                   x@.take((i + 1) as int).filter(|k:u64| k%3 == 0));
        }
        i += 1;
    }
    /* code modified by LLM (iteration 2): wrapped proof function call in proof block */
    proof {
        lemma_seq_take_all(x@);
    }
    assert(i == x.len());
    assert(x@.take(i as int) == x@);
}
}

fn main() {}