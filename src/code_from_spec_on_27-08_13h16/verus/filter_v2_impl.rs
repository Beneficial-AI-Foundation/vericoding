use vstd::prelude::*;

verus!{

// <vc-helpers>
proof fn lemma_seq_take_ascend<T>(v: Seq<T>, i: int)
    requires
        0 < i <= v.len(),
    ensures
        v.take(i as int).drop_last() == v.take(i-1),
{
    assert(v.take(i as int).drop_last() =~= v.take(i-1));
}

proof fn lemma_seq_take_all<T>(v: Seq<T>)
    ensures
        v == v.take(v.len() as int),
{
    assert(v =~= v.take(v.len() as int));
}

proof fn lemma_seq_filter_len<T>(s: Seq<T>, f: spec_fn(T) -> bool)
    ensures
        s.filter(f).len() <= s.len(),
{
    assert(s.filter(f).len() <= s.len());
}

proof fn lemma_seq_filter_append<T>(s1: Seq<T>, s2: Seq<T>, f: spec_fn(T) -> bool)
    ensures
        (s1 + s2).filter(f) == s1.filter(f) + s2.filter(f),
{
    assert((s1 + s2).filter(f) =~= s1.filter(f) + s2.filter(f));
}

proof fn lemma_seq_take_filter<T>(s: Seq<T>, i: int, f: spec_fn(T) -> bool)
    requires
        0 <= i <= s.len(),
    ensures
        s.take(i).filter(f) == s.filter(f).take(s.take(i).filter(f).len()),
{
    assert(s.take(i).filter(f).len() <= i);
    if i == 0 {
        assert(s.take(0).filter(f).len() == 0);
        assert(s.filter(f).take(0) == Seq::empty());
    } else if i == s.len() {
        assert(s.take(i).filter(f) == s.filter(f));
        assert(s.filter(f).take(s.filter(f).len()) == s.filter(f));
    } else {
        assert(s.take(i).filter(f).len() <= s.filter(f).len());
    }
}
// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)
    // pre-conditions-start
    requires 
        old(y).len() == 0,
    // pre-conditions-end
    // post-conditions-start
    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            y@ == x@.take(i as int).filter(|k: u64| k % 3 == 0),
        decreases
            x.len() - i,
    {
        if x[i] % 3 == 0 {
            y.push(x[i]);
        }
        i = i + 1;
    }
    proof {
        lemma_seq_take_all(x@);
        assert(y@ == x@.filter(|k: u64| k % 3 == 0));
    }
}
// </vc-code>

}

fn main() {}