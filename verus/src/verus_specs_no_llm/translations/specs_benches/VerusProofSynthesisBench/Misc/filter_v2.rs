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
    // TODO: Remove this comment and implement the function body
}
}


fn main() {}