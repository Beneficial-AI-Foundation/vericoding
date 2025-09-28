use vstd::prelude::*;

verus! {

spec fn sum_r(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

spec fn sum_l(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        s[0] + sum_l(s.subrange(1, s.len() as int))
    }
}


spec fn sum_v(v: Seq<int>, c: int, f: int) -> int
{
    if 0 <= c <= f <= v.len() {
        sum_r(v.subrange(c, f))
    } else {
        0
    }
}

// <vc-helpers>
proof fn lemma_sum_r_append(s: Seq<int>, x: int)
    ensures sum_r(s.push(x)) == sum_r(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x).len() == 1);
        assert(s.push(x).subrange(0, 0) == Seq::<int>::empty());
        assert(sum_r(Seq::<int>::empty()) == 0);
        assert(s.push(x)[0] == x);
        assert(sum_r(s) == 0);
    } else {
        let s_plus_x = s.push(x);
        assert(s_plus_x.len() == s.len() + 1);
        assert(s_plus_x[s_plus_x.len() - 1] == x);
        assert(s_plus_x.subrange(0, s_plus_x.len() - 1) == s);
    }
}

proof fn lemma_sum_r_empty()
    ensures sum_r(Seq::<int>::empty()) == 0
{
}

proof fn lemma_sum_r_single(x: int)
    ensures sum_r(seq![x]) == x
{
    assert(seq![x].len() == 1);
    assert(seq![x].subrange(0, 0) == Seq::<int>::empty());
    lemma_sum_r_empty();
}

proof fn lemma_subrange_extend(s: Seq<int>, i: int)
    requires 0 <= i < s.len()
    ensures s.subrange(0, i + 1) == s.subrange(0, i).push(s[i])
{
}
// </vc-helpers>

// <vc-spec>
fn sum_elems_b(v: &[i32]) -> (sum: i32)
//ensures sum as int == sum_l(v@.map(|i, x| x as int))
ensures sum as int == sum_r(v@.map(|i, x| x as int))
// </vc-spec>
// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i = 0;
    
    while i < v.len()
        invariant 
            0 <= i <= v.len(),
            sum as int == sum_r(v@.subrange(0, i as int).map(|j, x| x as int)),
            forall |k: int| 0 <= k < v.len() ==> -1000000 <= v@[k] <= 1000000,
            -1000000000 <= sum as int <= 1000000000
        decreases v.len() - i
    {
        proof {
            let mapped_v = v@.map(|j, x| x as int);
            let old_subrange = mapped_v.subrange(0, i as int);
            let new_subrange = mapped_v.subrange(0, (i + 1) as int);
            
            lemma_subrange_extend(mapped_v, i as int);
            assert(new_subrange == old_subrange.push(mapped_v[i as int]));
            assert(mapped_v[i as int] == v@[i as int] as int);
            
            lemma_sum_r_append(old_subrange, v@[i as int] as int);
            assert(sum_r(new_subrange) == sum_r(old_subrange) + v@[i as int] as int);
            assert(sum as int == sum_r(old_subrange));
            
            // Overflow check
            assert(sum as int + v@[i as int] as int <= 1000000000 + 1000000);
            assert(sum as int + v@[i as int] as int >= -1000000000 - 1000000);
        }
        
        sum = sum + v[i];
        i = i + 1;
    }
    
    proof {
        let mapped_v = v@.map(|i, x| x as int);
        assert(v@.subrange(0, v.len() as int) == v@);
        assert(mapped_v.subrange(0, v.len() as int) == mapped_v);
    }
    
    sum
}
// </vc-code>

fn main() {
}

}