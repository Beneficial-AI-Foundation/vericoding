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
proof fn sum_r_prefix_step(s: Seq<int>, n: int)
    requires
        0 <= n < s.len(),
    ensures
        sum_r(s.subrange(0, n + 1)) == sum_r(s.subrange(0, n)) + s[n],
{
    let t = s.subrange(0, n + 1);
    assert(t.len() == n + 1);
    assert(sum_r(t) == if t.len() == 0 {
        0
    } else {
        sum_r(t.subrange(0, t.len() - 1)) + t[t.len() - 1]
    });
    assert(t.len() > 0);
    assert(t.len() - 1 == n);
    assert(t.subrange(0, t.len() - 1) == s.subrange(0, n));
    assert(t[t.len() - 1] == s[n]);
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
    let s_seq = v@.map(|i, x| x as int);
    let mut i: usize = 0;
    let mut sum: i32 = 0;

    assert(s_seq.len() == v.len() as int);

    while i < v.len()
        invariant
            i <= v.len(),
            sum as int == sum_r(s_seq.subrange(0, i as int)),
        decreases v.len() - i
    {
        let xi = v[i];
        let old_i = i;
        let old_sum = sum;

        proof {
            assert(0 <= old_i as int && old_i as int < s_seq.len());
            sum_r_prefix_step(s_seq, old_i as int);
            assert(v@[old_i] == xi);
            assert(s_seq[old_i as int] == v@[old_i] as int);
        }

        sum = sum + xi;
        i = i + 1;

        proof {
            assert(old_sum as int == sum_r(s_seq.subrange(0, old_i as int)));
            assert(xi as int == s_seq[old_i as int]);
            assert(sum as int == old_sum as int + xi as int);
            assert(sum as int == sum_r(s_seq.subrange(0, old_i as int)) + s_seq[old_i as int]);
            assert(sum as int == sum_r(s_seq.subrange(0, i as int)));
        }
    }

    proof {
        assert(i == v.len());
        assert(s_seq.subrange(0, v.len() as int) == s_seq);
        assert(sum as int == sum_r(s_seq));
    }

    sum
}
// </vc-code>

fn main() {}

}