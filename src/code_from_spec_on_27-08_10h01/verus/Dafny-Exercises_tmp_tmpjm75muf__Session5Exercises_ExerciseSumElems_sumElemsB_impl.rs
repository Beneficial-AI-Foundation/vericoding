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
proof fn sum_r_append_lemma(s: Seq<int>, x: int)
    ensures sum_r(s.push(x)) == sum_r(s) + x
    decreases s.len()
{
    if s.len() == 0 {
        assert(s.push(x) == seq![x]);
        assert(sum_r(s.push(x)) == x);
        assert(sum_r(s) == 0);
    } else {
        let s_extended = s.push(x);
        assert(s_extended.len() == s.len() + 1);
        assert(s_extended[s_extended.len() - 1] == x);
        assert(s_extended.subrange(0, s_extended.len() - 1) == s);
        assert(sum_r(s_extended) == sum_r(s) + x);
    }
}

proof fn sum_r_build_up_lemma(v: &[i32], i: usize)
    requires i <= v.len()
    ensures sum_r(v@.subrange(0, i as int).map(|j, x| x as int)) == 
            if i == 0 { 0 } else { 
                sum_r(v@.subrange(0, (i-1) as int).map(|j, x| x as int)) + v[i-1] as int 
            }
{
    if i == 0 {
        assert(v@.subrange(0, 0).len() == 0);
    } else {
        let prev_seq = v@.subrange(0, (i-1) as int).map(|j, x| x as int);
        let curr_seq = v@.subrange(0, i as int).map(|j, x| x as int);
        assert(curr_seq == prev_seq.push(v[i-1] as int));
        sum_r_append_lemma(prev_seq, v[i-1] as int);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn sum_elems_b(v: &[i32]) -> (sum: i32)
//ensures sum as int == sum_l(v@.map(|i, x| x as int))
ensures sum as int == sum_r(v@.map(|i, x| x as int))
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < v.len()
        invariant 
            i <= v.len(),
            sum as int == sum_r(v@.subrange(0, i as int).map(|j, x| x as int))
    {
        proof {
            sum_r_build_up_lemma(v, i + 1);
        }
        sum = sum + v[i];
        i = i + 1;
    }
    
    proof {
        assert(v@.subrange(0, v.len() as int) == v@);
    }
    
    sum
}
// </vc-code>

fn main() {
}

}