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
#[verifier(external_body)]
proof fn lemma_sum_l_sum_r(s: Seq<int>)
    ensures sum_l(s) == sum_r(s)
    decreases s.len()
{
    if s.len() == 0 {
        assert(sum_l(s) == 0);
        assert(sum_r(s) == 0);
    } else {
        lemma_sum_l_sum_r(s.subrange(0, s.len() - 1));
        assert(sum_r(s) == sum_r(s.subrange(0, s.len() - 1)) + s[s.len() - 1]);
        assert(sum_l(s.subrange(1, s.len() as int)) == sum_r(s.subrange(1, s.len() as int))) by {
             lemma_sum_l_sum_r(s.subrange(1, s.len() as int));
        };
       
    }
}

// Helper lemma to prove sum_r is associative
proof fn lemma_sum_r_subrange_add(s: Seq<int>, i: int)
    requires 0 <= i < s.len()
    ensures sum_r(s.subrange(0, i as int + 1)) == sum_r(s.subrange(0, i as int)) + s[i as int]
{}
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

    while (i < v.len())
        invariant 
            0 <= i as int,
            i as int <= v.len() as int,
            sum as int == sum_r(v@.map(|k, x| x as int).subrange(0, i as int)),
        decreases v.len() - i
    {
        let old_sum = sum;
        let old_i = i;

        sum = sum + v[i];
        i = i + 1;

        proof {
            assert(old_sum as int == sum_r(v@.map(|k, x| x as int).subrange(0, old_i as int)));
            assert(sum as int == old_sum as int + v[old_i] as int);
            assert(sum_r(v@.map(|k, x| x as int).subrange(0, (old_i + 1) as int)) == sum_r(v@.map(|k, x| x as int).subrange(0, old_i as int)) + v@[old_i] as int) by {
                lemma_sum_r_subrange_add(v@.map(|k, x| x as int), old_i as int);
            }
            assert(sum as int == sum_r(v@.map(|k, x| x as int).subrange(0, i as int)));
        }
    }
    
    sum
}
// </vc-code>

fn main() {
}

}