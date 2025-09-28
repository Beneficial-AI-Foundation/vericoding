use vstd::prelude::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
}

spec fn is_even(i: int) -> bool
    recommends i >= 0
{
    i % 2 == 0
}

spec fn count_even(s: Seq<int>) -> int
    recommends positive(s)
    decreases s.len()
{
    if s.len() == 0 {
        0 as int
    } else {
        (if s[s.len() - 1] % 2 == 0 { 1 as int } else { 0 as int }) + count_even(s.subrange(0, s.len() - 1))
    }
}

// <vc-helpers>
proof fn count_even_preserves_positive(s: Seq<int>)
    requires positive(s), s.len() > 0
    ensures positive(s.subrange(0, s.len() - 1))
{
    let sub = s.subrange(0, s.len() - 1);
    assert forall|u: int| 0 <= u < sub.len() implies sub[u] >= 0 by {
        assert(sub[u] == s[u]);
    }
}

proof fn count_even_step(s: Seq<int>, last_elem: int)
    requires positive(s), s.len() > 0, last_elem == s[s.len() - 1]
    ensures count_even(s) == (if last_elem % 2 == 0 { 1int } else { 0int }) + count_even(s.subrange(0, s.len() - 1))
{
    count_even_preserves_positive(s);
}

proof fn vec_to_seq_positive(v: &Vec<i32>)
    requires positive(v@.map(|i: int, x: i32| x as int))
    ensures forall|k: int| 0 <= k < v.len() ==> v[k] >= 0
{
    let mapped = v@.map(|i: int, x: i32| x as int);
    assert forall|k: int| 0 <= k < v.len() implies v[k] >= 0 by {
        assert(mapped[k] == v[k] as int);
        assert(v[k] as int >= 0);
    }
}

proof fn count_even_loop_invariant(v: &Vec<i32>, i: usize, count: i32)
    requires 
        positive(v@.map(|i: int, x: i32| x as int)),
        i <= v.len(),
        count as int == count_even(v@.subrange(0, i as int).map(|j: int, x: i32| x as int))
    ensures
        positive(v@.subrange(0, i as int).map(|j: int, x: i32| x as int))
{
    let sub_seq = v@.subrange(0, i as int);
    let mapped_sub = sub_seq.map(|j: int, x: i32| x as int);
    
    assert forall|u: int| 0 <= u < mapped_sub.len() implies mapped_sub[u] >= 0 by {
        assert(mapped_sub[u] == sub_seq[u] as int);
        assert(sub_seq[u] == v@[u]);
        assert(v@[u] as int >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn mcount_even(v: &Vec<i32>) -> (n: i32)
    requires positive(v@.map(|i: int, x: i32| x as int))
    ensures n as int == count_even(v@.map(|i: int, x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    proof {
        vec_to_seq_positive(v);
    }
    
    let mut count: i32 = 0;
    let mut i: usize = 0;
    
    while i < v.len()
        invariant
            i <= v.len(),
            count as int == count_even(v@.subrange(0, i as int).map(|j: int, x: i32| x as int)),
            positive(v@.map(|k: int, x: i32| x as int))
    {
        count_even_loop_invariant(v, i, count);
        
        if v[i] % 2 == 0 {
            count = count + 1;
        }
        
        let old_i = i;
        i = i + 1;
        
        proof {
            let current_subrange = v@.subrange(0, i as int).map(|j: int, x: i32| x as int);
            let prev_subrange = v@.subrange(0, old_i as int).map(|j: int, x: i32| x as int);
            
            assert(current_subrange == prev_subrange.push(v@[old_i as int] as int));
            
            count_even_preserves_positive(current_subrange);
            count_even_step(current_subrange, v@[old_i as int] as int);
            
            assert(count_even(current_subrange) == 
                   (if v@[old_i as int] % 2 == 0 { 1int } else { 0int }) + count_even(prev_subrange));
        }
    }
    
    assert(v@.subrange(0, i as int) == v@);
    assert(v@.subrange(0, i as int).map(|j: int, x: i32| x as int) == v@.map(|j: int, x: i32| x as int));
    
    count
}
// </vc-code>

fn main() {
}

}