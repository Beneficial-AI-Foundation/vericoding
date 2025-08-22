use vstd::prelude::*;
fn main() {}

verus!{

proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
    requires
        0< i <= v.len(),
    ensures
        v.take(i as int).drop_last() == v.take(i-1),
{
    // v.take(i) gives us the first i elements
    // v.take(i).drop_last() gives us the first i-1 elements
    // v.take(i-1) also gives us the first i-1 elements
    // These are equal by the definitions of take and drop_last
    assert(v.take(i as int).len() == i);
    assert(v.take(i as int).drop_last().len() == i - 1);
    assert(v.take(i-1).len() == i - 1);
    
    // Show that elements are equal at each position
    assert forall |j: int| 0 <= j < i - 1 implies 
        v.take(i as int).drop_last()[j] == v.take(i-1)[j] by {
        assert(v.take(i as int).drop_last()[j] == v.take(i as int)[j]);
        assert(v.take(i as int)[j] == v[j]);
        assert(v.take(i-1)[j] == v[j]);
    };
}

proof fn lemma_seq_take_all<T>(v: Seq<T>)
    ensures
        v == v.take(v.len() as int),
{
    // Taking all elements should give us the original sequence
    assert(v.take(v.len() as int).len() == v.len());
    assert forall |i: int| 0 <= i < v.len() implies 
        v[i] == v.take(v.len() as int)[i] by {
        // By definition of take, v.take(n)[i] == v[i] for i < n
    };
}

pub fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
requires 
    old(y).len() == 0,
ensures 
    y@ == x@.filter(|k:u64| k%3 == 0),
{
    for i in 0..x.len()
        invariant
            y@ == x@.subrange(0, i as int).filter(|k:u64| k%3 == 0),
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
    }
}
}