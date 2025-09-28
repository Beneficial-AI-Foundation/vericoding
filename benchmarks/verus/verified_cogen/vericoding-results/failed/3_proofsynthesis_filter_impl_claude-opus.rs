// <vc-preamble>
use vstd::prelude::*;

verus!{
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma to prove filter distribution over push */
proof fn lemma_filter_push(s: Seq<u64>, v: u64)
    ensures
        s.push(v).filter(|k: u64| k % 3 == 0) == if v % 3 == 0 { s.filter(|k: u64| k % 3 == 0).push(v) } else { s.filter(|k: u64| k % 3 == 0) }
{
    assert(s.push(v) =~= s + seq![v]);
    assert((s + seq![v]).filter(|k: u64| k % 3 == 0) =~= s.filter(|k: u64| k % 3 == 0) + seq![v].filter(|k: u64| k % 3 == 0));
    if v % 3 == 0 {
        assert(seq![v].filter(|k: u64| k % 3 == 0) =~= seq![v]);
    } else {
        assert(seq![v].filter(|k: u64| k % 3 == 0) =~= seq![]);
    }
}
// </vc-helpers>

// <vc-spec>
fn myfun4(x: &Vec<u64>, y: &mut Vec<u64>)

    requires 
        old(y).len() == 0,

    ensures 
        y@ == x@.filter(|k:u64| k%3 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use helper lemma to prove filter properties */
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            y@ == x@.take(i as int).filter(|k: u64| k % 3 == 0),
        decreases x.len() - i,
    {
        let ghost old_y = y@;
        let ghost old_take = x@.take(i as int);
        
        if x[i] % 3 == 0 {
            y.push(x[i]);
            proof {
                assert(x@.take((i + 1) as int) == old_take.push(x@[i as int]));
                lemma_filter_push(old_take, x@[i as int]);
                assert(old_take.push(x@[i as int]).filter(|k: u64| k % 3 == 0) == old_take.filter(|k: u64| k % 3 == 0).push(x@[i as int]));
                assert(y@ == old_y.push(x@[i as int]));
                assert(y@ == x@.take((i + 1) as int).filter(|k: u64| k % 3 == 0));
            }
        } else {
            proof {
                assert(x@.take((i + 1) as int) == old_take.push(x@[i as int]));
                assert(x@[i as int] % 3 != 0);
                lemma_filter_push(old_take, x@[i as int]);
                assert(old_take.push(x@[i as int]).filter(|k: u64| k % 3 == 0) == old_take.filter(|k: u64| k % 3 == 0));
                assert(y@ == old_y);
                assert(y@ == x@.take((i + 1) as int).filter(|k: u64| k % 3 == 0));
            }
        }
        i = i + 1;
    }
    assert(x@.take(x.len() as int) == x@);
}
// </vc-code>

}
fn main() {}