// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1 as int } else { 0 as int })
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn count_rec_property(a: Seq<int>, x: int, i: int)
    requires
        0 <= i <= a.len(),
    ensures
        count_rec(a.subrange(0, i), x) + count_rec(a.subrange(i, a.len() as int), x) == count_rec(a, x),
    decreases a.len() - i
{
    if i == 0 {
        assert(a.subrange(0, 0) =~= Seq::<int>::empty());
        assert(count_rec(a.subrange(0, 0), x) == 0);
        assert(a.subrange(0, a.len() as int) =~= a);
    } else if i == a.len() {
        assert(a.subrange(a.len() as int, a.len() as int) =~= Seq::<int>::empty());
        assert(count_rec(a.subrange(a.len() as int, a.len() as int), x) == 0);
        assert(a.subrange(0, a.len() as int) =~= a);
    } else {
        count_rec_property(a.subrange(1, a.len() as int), x, i - 1);
    }
}

proof fn count_rec_append(a: Seq<int>, b: Seq<int>, x: int)
    ensures
        count_rec(a + b, x) == count_rec(a, x) + count_rec(b, x),
    decreases a.len()
{
    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        let tail_a = a.subrange(1, a.len() as int);
        assert((a + b).subrange(1, (a + b).len() as int) =~= tail_a + b);
        count_rec_append(tail_a, b, x);
    }
}
// </vc-helpers>

// <vc-spec>
fn count(a: Vec<i8>, x: i8) -> (cnt: i8)
    ensures 
        cnt as int == count_rec(a@.map(|i: int, v: i8| v as int), x as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): use usize for vector indexing instead of int */
{
    let mut cnt: i8 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            cnt as int == count_rec(a@.subrange(0, i as int).map(|j: int, v: i8| v as int), x as int),
        decreases a.len() - i
    {
        if a[i] == x {
            cnt = cnt + 1;
        }
        
        proof {
            let mapped_seq = a@.map(|j: int, v: i8| v as int);
            let prev_subrange = mapped_seq.subrange(0, i as int);
            let next_subrange = mapped_seq.subrange(0, (i + 1) as int);
            
            assert(next_subrange =~= prev_subrange.push(mapped_seq[i as int]));
            assert(mapped_seq[i as int] == a[i] as int);
            
            if a[i] == x {
                assert(count_rec(next_subrange, x as int) == count_rec(prev_subrange, x as int) + 1);
            } else {
                assert(count_rec(next_subrange, x as int) == count_rec(prev_subrange, x as int));
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(a@.subrange(0, a.len() as int) =~= a@);
    }
    
    cnt
}
// </vc-code>


}

fn main() {}