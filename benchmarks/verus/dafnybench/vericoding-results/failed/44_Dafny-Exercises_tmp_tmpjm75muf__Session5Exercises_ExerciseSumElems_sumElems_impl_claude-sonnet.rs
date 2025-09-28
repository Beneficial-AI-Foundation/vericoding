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

spec fn sum_v(v: Seq<int>, c: int, f: int) -> int {
    if 0 <= c <= f <= v.len() {
        sum_r(v.subrange(c, f))
    } else {
        0
    }
}

// <vc-helpers>
proof fn sum_r_append(s1: Seq<int>, s2: Seq<int>)
    ensures sum_r(s1 + s2) == sum_r(s1) + sum_r(s2)
    decreases s2.len()
{
    if s2.len() == 0 {
        assert(s1 + s2 =~= s1);
    } else {
        let combined = s1 + s2;
        let s2_prefix = s2.subrange(0, s2.len() - 1);
        let s1_plus_prefix = s1 + s2_prefix;
        assert(combined.subrange(0, combined.len() - 1) =~= s1_plus_prefix);
        assert(combined[combined.len() - 1] == s2[s2.len() - 1]);
        sum_r_append(s1, s2_prefix);
    }
}

proof fn sum_r_single(x: int)
    ensures sum_r(seq![x]) == x
{
    let s = seq![x];
    assert(s.len() == 1);
    assert(s.subrange(0, 0) =~= seq![]);
    assert(sum_r(s.subrange(0, 0)) == 0);
    assert(s[0] == x);
}

proof fn sum_r_extend(s: Seq<int>, x: int)
    ensures sum_r(s + seq![x]) == sum_r(s) + x
{
    sum_r_append(s, seq![x]);
    sum_r_single(x);
}
// </vc-helpers>

// <vc-spec>
fn sum_elems(v: &[i32]) -> (sum: i32)
//ensures sum as int == sum_l(v@.map(|i, x| x as int))
ensures sum as int == sum_r(v@.map(|i, x| x as int))
//ensures sum as int == sum_v(v@.map(|i, x| x as int), 0, v@.len())
// </vc-spec>
// <vc-code>
{
    let mut sum = 0i32;
    let mut i = 0;
    
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            sum as int == sum_r(v@.subrange(0, i as int).map(|j, x| x as int)),
            i < v.len() ==> v@[i as int] as int + sum as int <= i32::MAX,
            i < v.len() ==> v@[i as int] as int + sum as int >= i32::MIN
        decreases v.len() - i
    {
        let old_i = i;
        sum = sum + v[i];
        i = i + 1;
        
        proof {
            let mapped_subrange = v@.subrange(0, old_i as int).map(|j, x| x as int);
            let new_mapped_subrange = v@.subrange(0, i as int).map(|j, x| x as int);
            let new_elem = seq![v@[old_i as int] as int];
            
            assert(new_mapped_subrange =~= mapped_subrange + new_elem);
            sum_r_extend(mapped_subrange, v@[old_i as int] as int);
        }
    }
    
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
        assert(v@.map(|j, x| x as int) =~= v@.subrange(0, v@.len() as int).map(|j, x| x as int));
    }
    
    sum
}
// </vc-code>

fn main() {}

}