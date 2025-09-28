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
proof fn lemma_sum_r_equals_sum_l(s: Seq<int>)
    decreases s.len()
    ensures sum_r(s) == sum_l(s)
{
    if s.len() == 0 {
    } else {
        lemma_sum_r_equals_sum_l(s.subrange(0, s.len() - 1));
        lemma_sum_r_equals_sum_l(s.subrange(1, s.len()));
        
        let sub1 = s.subrange(0, s.len() - 1);
        let sub2 = s.subrange(1, s.len());
        
        assert(s.len() >= 1);
        assert(sum_r(s) == sum_r(sub1) + s[s.len() - 1]);
        assert(sum_l(s) == s[0] + sum_l(sub2));
        
        assert(sum_r(sub1) == sum_l(sub1));
        assert(sum_r(sub2) == sum_l(sub2));
        
        assert(sum_r(s) == sum_l(s));
    }
}

proof fn lemma_sum_equivalence(s: Seq<int>)
    requires s.len() > 0
    ensures s[0] + sum_l(s.subrange(1, s.len())) == sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.subrange(1, 1) =~= Seq::empty());
        assert(s.subrange(0, 0) =~= Seq::empty());
        assert(sum_l(Seq::empty()) == 0);
        assert(sum_r(Seq::empty()) == 0);
        assert(s[0] == s[s.len() - 1]);
    } else {
        let sub = s.subrange(1, s.len());
        lemma_sum_equivalence(sub);
        
        assert(s[0] + sum_l(sub) == s[0] + (sum_r(sub.subrange(0, sub.len() - 1)) + sub[sub.len() - 1]));
        assert(sub[sub.len() - 1] == s[s.len() - 1]);
        assert(sum_r(s.subrange(0, s.len() - 1)) == sum_r(sub.subrange(0, sub.len() - 1)) + s[0]);
    }
}

proof fn lemma_sum_v_properties(v: Seq<int>, c: int, f: int)
    requires 0 <= c <= f <= v.len()
    ensures sum_v(v, c, f) == sum_r(v.subrange(c, f))
{
}

proof fn lemma_sum_r_base_case() 
    ensures sum_r(Seq::empty()) == 0
{
}

proof fn lemma_sum_r_recursive_case(s: Seq<int>)
    requires s.len() > 0
    ensures sum_r(s) == sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
{
}

proof fn lemma_sum_v_step(v: Seq<int>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        sum_v(v, 0, i + 1) == sum_v(v, 0, i) + v[i as nat]
{
    if v.len() > 0 {
        assert(v.subrange(0, i + 1) =~= v.subrange(0, i).push(v[i as nat]));
        lemma_sum_r_recursive_case(v.subrange(0, i + 1));
        assert(sum_r(v.subrange(0, i + 1)) == sum_r(v.subrange(0, i)) + v[i as nat]);
        lemma_sum_v_properties(v, 0, i);
        lemma_sum_v_properties(v, 0, i + 1);
        assert(sum_v(v, 0, i + 1) == sum_r(v.subrange(0, i + 1)));
        assert(sum_v(v, 0, i) == sum_r(v.subrange(0, i)));
    }
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
    let mut i: usize = 0;
    let mapped_seq = v@.map(|idx, x| x as int);
    
    while i < v.len()
        invariant 
            0 <= i <= v.len(),
            sum as int == sum_v(mapped_seq, 0, i as int),
        decreases v.len() - i
    {
        lemma_sum_v_properties(mapped_seq, 0, i as int);
        lemma_sum_v_step(mapped_seq, i as int);
        
        sum = sum + v[i];
        i = i + 1;
        
        assert(sum as int == sum_v(mapped_seq, 0, (i - 1) as int) + v@[i - 1] as int);
        assert(sum as int == sum_v(mapped_seq, 0, i as int));
    }
    
    lemma_sum_r_equals_sum_l(mapped_seq);
    lemma_sum_v_properties(mapped_seq, 0, v.len() as int);
    
    sum
}
// </vc-code>

fn main() {
}

}